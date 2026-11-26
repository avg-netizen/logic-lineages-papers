module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowRegistryTuple PrescribedRuntimeEquality PrescribedRuntimeCallCongruence HistoryRuleSuffix

/-- Literal ordinary unary recipe: inner MP consumes the supplied code, outer
MP consumes reflexivity. Not the implication-producing successor helper. -/
def unary {n inputs arity : Nat} (e : FixedFormulaSubstitution.Environment n 1 inputs)
 (f : Term n) (raw : List.Vector (Program arity) inputs) (t u code : Program arity) : Program arity :=
 let term (env : FixedFormulaSubstitution.Environment n 0 (inputs+1)) (xs : List.Vector (Program arity) (inputs+1)) :=
  Program.composition (FixedFormulaSubstitution.termProgram env f) xs.get
 let ft := term (UniformRuntimeEnvironmentAgreement.specialize e) (t ::ᵥ raw)
 let fu := term (UniformRuntimeEnvironmentAgreement.specialize e) (u ::ᵥ raw)
 let openCode := Program.composition (FixedFormulaSubstitution.termProgram e f) raw.get
 let eq := FixedFormulaSubstitution.binary 0
 let imp := FixedFormulaSubstitution.binary 7
 CurrentRecursionBaseProgram.mp (eq ft fu)
  (CurrentRecursionBaseProgram.mp (imp (eq ft ft) (eq ft fu))
   (CurrentRecursionBaseProgram.replacement (eq ft openCode) t u) code)
  (CurrentRecursionStepProgram.reflexivity ft)
def unaryClosed {arity : Nat} (f : Term 1) (t u code : Program arity) : Program arity :=
 unary boundEnvironment f nil t u code
def binary {arity : Nat} (multiply : Bool) (a b c d hac hbd : Program arity) : Program arity :=
 let op := FixedFormulaSubstitution.binary (if multiply then 4 else 3)
 let hp := unary binaryEnvironment (binaryTerm multiply (.var 0) (.var 1)) (b ::ᵥ nil) a c hac
 let hq := unary binaryEnvironment (binaryTerm multiply (.var 1) (.var 0)) (c ::ᵥ nil) b d hbd
 CurrentRecursionBaseProgram.transitivity (op a b) (op c b) (op c d) hp hq
def pairCode {arity : Nat} (a b : Program arity) : Program arity :=
 let add := FixedFormulaSubstitution.binary 3
 let mul := FixedFormulaSubstitution.binary 4
 add (mul (add a b) (add a b)) a
def pair {arity : Nat} (a b c d hac hbd : Program arity) : Program arity :=
 let add := FixedFormulaSubstitution.binary 3
 let mul := FixedFormulaSubstitution.binary 4
 let hs := binary false a b c d hac hbd
 let hm := binary true (add a b) (add a b) (add c d) (add c d) hs hs
 binary false (mul (add a b) (add a b)) a (mul (add c d) (add c d)) c hm hac
def rawZero (arity : Nat) : Program arity := constant arity (Encodable.encode (GorbowTermPrefixCode.encode (Term.zero : Term 0)))
def tupleCode {arity : Nat} : {n : Nat} → List.Vector (Program arity) n → Program arity
 | 0, _ => rawZero arity
 | n+1, xs => FixedFormulaSubstitution.unary 2 (pairCode xs.head (tupleCode xs.tail))
def tuple {arity : Nat} : {n : Nat} → List.Vector (Program arity) n → List.Vector (Program arity) n → List.Vector (Program arity) n → Program arity
 | 0, _, _, _ => CurrentRecursionStepProgram.reflexivity (rawZero arity)
 | n+1, xs, ys, codes => unaryClosed (.succ (.var 0))
  (pairCode xs.head (tupleCode xs.tail)) (pairCode ys.head (tupleCode ys.tail))
  (pair xs.head (tupleCode xs.tail) ys.head (tupleCode ys.tail) codes.head (tuple xs.tail ys.tail codes.tail))
def callConstructor {arity n : Nat} (tag : Program arity)
 (xs ys codes : List.Vector (Program arity) n) : Program arity :=
 let tagRaw := applyOne LiteralNumeralPrefix.numeralCode tag
 let arityRaw := constant arity (Encodable.encode (GorbowTermPrefixCode.encode (Term.numeral n : Term 0)))
 let xt := tupleCode xs
 let yt := tupleCode ys
 let hp := pair tagRaw xt tagRaw yt (CurrentRecursionStepProgram.reflexivity tagRaw) (tuple xs ys codes)
 let hh := pair arityRaw (pairCode tagRaw xt) arityRaw (pairCode tagRaw yt)
  (CurrentRecursionStepProgram.reflexivity arityRaw) hp
 unaryClosed (.universalFunction (.var 0)) (pairCode arityRaw (pairCode tagRaw xt))
  (pairCode arityRaw (pairCode tagRaw yt)) hh

/-- Three contiguous blocks: left raw terms, right raw terms, unrestricted codes. -/
def width (n : Nat) := n+(n+n)
def leftInputs (n : Nat) : List.Vector (Program (width n)) n :=
 List.Vector.ofFn (fun i => .projection (i.castAdd (n+n)))
def rightInputs (n : Nat) : List.Vector (Program (width n)) n :=
 List.Vector.ofFn (fun i => .projection (Fin.natAdd n (i.castAdd n)))
def codeInputs (n : Nat) : List.Vector (Program (width n)) n :=
 List.Vector.ofFn (fun i => .projection (Fin.natAdd n (Fin.natAdd n i)))
def tupleProgram (n : Nat) : Program (width n) := tuple (leftInputs n) (rightInputs n) (codeInputs n)
def tailProgram {arity : Nat} (q : Program arity) : Program (arity+1) :=
 .composition q (fun i => .projection i.succ)
def callProgram (n : Nat) : Program (width n+1) :=
 callConstructor (.projection 0) ((leftInputs n).map tailProgram)
  ((rightInputs n).map tailProgram) ((codeInputs n).map tailProgram)
def pack {α : Type} {n : Nat} (xs ys codes : List.Vector α n) : List.Vector α (width n) := xs ++ (ys ++ codes)
def encodeTerms {n : Nat} (xs : List.Vector (Term 0) n) : List.Vector Nat n :=
 xs.map (fun t => Encodable.encode (GorbowTermPrefixCode.encode t))

/-- Separate reflexivity-cons address is allowed and backed by its own membership. -/
abbrev Tags := PrescribedRuntimeCallCongruence.Tags
structure Installation {arity : Nat} (p : Program arity) (J : Tags) : Prop where
 hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩
 ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩
 hn : (nodes p)[J.numeralTag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩
 hm : (nodes p)[J.mtag]? = some ⟨4,LiteralRawMP.constructor⟩
 h12 : (nodes p)[J.constructorTag]? = some ⟨3,UniformClosedRule12.lineConstructor⟩
 hrc : (nodes p)[J.rctag]? = some ⟨2,HistoryCodec.cons⟩
 hr : (nodes p)[J.reflexivityTag]? = some ⟨1,RawReflexivity.lineConstructor⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram
