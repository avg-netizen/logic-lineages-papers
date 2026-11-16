module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCalculationFormulaProgram.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowRegistryTuple PrescribedRuntimeEquality PrescribedRuntimeCallCongruence HistoryRuleSuffix

/-- Dynamic target identifier is a term, not a preselected registry address. -/
def openCall {ctx m : Nat} (tag : Term ctx) (args : List.Vector (Term ctx) m) : Term ctx :=
 .universalFunction (pairTerm (Term.numeral m) (pairTerm tag (tupleTerm args.toList)))
/-- First m variables are original inputs, last variable is runtime node tag. -/
def rootTemplate (m : Nat) : Formula (m+1) :=
 let xs := List.Vector.ofFn (fun i : Fin m => (Term.var i.castSucc : Term (m+1)))
 .equal (openCall (.var (Fin.last m)) (.zero ::ᵥ xs))
  (openCall (.succ (.var (Fin.last m))) xs)
def quote {n arity : Nat} (f : Formula n) (raw : Fin n → Program arity) : Program arity :=
 .composition (FixedFormulaSubstitution.formulaProgram f (PrescribedRuntimeSpecialization.runtimeEnvironment n)) raw
def headQuote {n arity : Nat} (f : Formula (n+1)) (raw : Fin n → Program arity) : Program arity :=
 .composition (FixedFormulaSubstitution.formulaProgram f (PrescribedRuntimeSpecialization.headEnvironment n)) raw
def singleton {arity : Nat} (line : Program arity) : Program arity :=
 applyTwo HistoryCodec.cons line (constant arity 0)
/-- Literal original rule4 axiom line, including the singleton raw argument. -/
def axiomProgram {arity : Nat} (raw : Program arity) : Program arity :=
 singleton (applyTwo HistoryCodec.pair (constant arity 0)
  (applyTwo HistoryCodec.pair raw (applyTwo HistoryCodec.pair (constant arity 4)
   (applyTwo HistoryCodec.pair (constant arity 0)
    (applyTwo HistoryCodec.pair (singleton raw)
     (applyTwo HistoryCodec.pair (constant arity 0) (constant arity 0)))))))
def mp {arity : Nat} (formula imp ant : Program arity) : Program arity :=
 .composition LiteralRawMP.constructor
  (Fin.cases (constant arity 0) (Fin.cases formula (Fin.cases imp (Fin.cases ant Fin.elim0))))
def allInstance {arity : Nat} (matrix replacement : Program arity) : Program arity :=
 singleton (.composition UniformClosedRule13.lineConstructor (Fin.cases matrix (Fin.cases replacement Fin.elim0)))
def replacement {arity : Nat} (matrix left right : Program arity) : Program arity :=
 singleton (.composition UniformClosedRule12.lineConstructor (Fin.cases matrix (Fin.cases left (Fin.cases right Fin.elim0))))
/-- Original tail-first binder specialization. The last variable is the tag
and is never universally closed by this recursion. -/
def seedProgram {arity : Nat} : (n : Nat) → Formula (n+1) → (Fin (n+1) → Program arity) → Program arity
 | 0, f, raw => axiomProgram (quote f raw)
 | n+1, f, raw => mp (quote f raw) (allInstance (headQuote f (fun i => raw i.succ)) (raw 0))
   (seedProgram n (.all f) (fun i => raw i.succ))
def transitivity {arity : Nat} (left middle right first second : Program arity) : Program arity :=
 let eq : Program arity → Program arity → Program arity := FixedFormulaSubstitution.binary 0
 let implication : Program arity → Program arity → Program arity := FixedFormulaSubstitution.binary 7
 let matrix := headQuote (.equal (.var 1) (.var 0) : Formula 2) (fun _ => left)
 mp (eq left right) (mp (implication (eq left middle) (eq left right))
  (replacement matrix middle right) second) first
/-- All numeric node tags are ordinary runtime arguments. -/
def childArguments (m : Nat) : Fin (m+1) → Program (m+1) :=
 Fin.cases (applyOne .succ (.projection 0)) (fun i => .projection i.succ)
def rawInputs (m : Nat) : Fin m → Program (m+1) :=
 fun i => applyOne LiteralNumeralPrefix.numeralCode (.projection i.succ)
def rootArguments (m : Nat) : Fin (m+1) → Program (m+1) :=
 Fin.lastCases (applyOne LiteralNumeralPrefix.numeralCode (.projection 0)) (rawInputs m)
def parentCode (m : Nat) : Program (m+1) :=
 .composition (FixedFormulaSubstitution.termProgram (PrescribedRuntimeSpecialization.runtimeEnvironment (m+1))
  (openCall (.var (Fin.last m)) (.zero ::ᵥ List.Vector.ofFn (fun i : Fin m => (Term.var i.castSucc : Term (m+1))))))
  (rootArguments m)
def childCode (m : Nat) : Program (m+1) :=
 .composition (FixedFormulaSubstitution.termProgram (PrescribedRuntimeSpecialization.runtimeEnvironment (m+1))
  (openCall (.succ (.var (Fin.last m))) (List.Vector.ofFn (fun i : Fin m => (Term.var i.castSucc : Term (m+1))))))
  (rootArguments m)
/-- Explicit original base recipe; the child producer is actually called at
(tag+1,inputs), not replaced by an arbitrary accepted certificate oracle. -/
def program {m : Nat} (base : Program m) (child : Program (m+1)) : Program (m+1) :=
 transitivity (parentCode m) (childCode m)
  (applyOne LiteralNumeralPrefix.numeralCode (CurrentCalculationFormulaProgram.tailProgram base))
  (seedProgram m (rootTemplate m) (rootArguments m))
  (.composition child (childArguments m))

structure Tags where
 ptag : Nat
 ctag : Nat
 atag : Nat
 ntag : Nat
 mtag : Nat
 r12 : Nat
 r13 : Nat
 baseTag : Nat
 childTag : Nat
structure Installation {arity m : Nat} (p : Program arity) (base : Program m) (child : Program (m+1)) (J : Tags) : Prop where
 hp : (nodes p)[J.ptag]? = some ⟨2,HistoryCodec.pair⟩
 hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩
 ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩
 hn : (nodes p)[J.ntag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩
 hm : (nodes p)[J.mtag]? = some ⟨4,LiteralRawMP.constructor⟩
 h12 : (nodes p)[J.r12]? = some ⟨3,UniformClosedRule12.lineConstructor⟩
 h13 : (nodes p)[J.r13]? = some ⟨2,UniformClosedRule13.lineConstructor⟩
 hb : (nodes p)[J.baseTag]? = some ⟨m,base⟩
 hchild : (nodes p)[J.childTag]? = some ⟨m+1,child⟩

def axiomValue {ctx : Nat} (J : Tags) (raw : Term ctx) : Term ctx :=
 HistoryLookup.consCall J.ctag (HistoryKernel.pairCall J.ptag .zero
  (HistoryKernel.pairCall J.ptag raw (HistoryKernel.pairCall J.ptag (Term.numeral 4)
   (HistoryKernel.pairCall J.ptag .zero (HistoryKernel.pairCall J.ptag (HistoryLookup.consCall J.ctag raw .zero)
    (HistoryKernel.pairCall J.ptag .zero .zero)))))) .zero
def seedValue {ctx : Nat} (J : Tags) : (n : Nat) → Formula (n+1) → List.Vector (Term ctx) (n+1) → Term ctx
 | 0, f, raw => axiomValue J (FixedFormulaSubstitution.formulaValue J.ctag J.atag raw f (PrescribedRuntimeSpecialization.runtimeEnvironment 1))
 | n+1, f, raw => LiteralMPRun.certificate J.mtag .zero
  (FixedFormulaSubstitution.formulaValue J.ctag J.atag raw f (PrescribedRuntimeSpecialization.runtimeEnvironment (n+2)))
  (UniformClosedRule13Certificate.certificate J.ctag J.r13
   (FixedFormulaSubstitution.formulaValue J.ctag J.atag raw.tail f (PrescribedRuntimeSpecialization.headEnvironment (n+1))) raw.head)
  (seedValue J n (.all f) raw.tail)
def rawValues {ctx m : Nat} (J : Tags) (target : Term ctx) (inputs : List.Vector (Term ctx) m) : List.Vector (Term ctx) (m+1) :=
 List.Vector.ofFn (Fin.lastCases (LiteralNumeralPrefix.numeralCall J.ntag target)
  (fun i => LiteralNumeralPrefix.numeralCall J.ntag (inputs.get i)))
def value {ctx m : Nat} (J : Tags) (target : Term ctx) (inputs : List.Vector (Term ctx) m) : Term ctx :=
 let K := CurrentCalculationFormulaProgram.codecTags J.ctag J.atag J.ntag
 let nums := inputs.map (LiteralNumeralPrefix.numeralCall J.ntag)
 transitivityCertificate J.mtag J.ctag J.atag J.r12
  (callValue K target (LiteralNumeralPrefix.numeralCall J.ntag .zero ::ᵥ nums))
  (callValue K (.succ target) nums)
  (LiteralNumeralPrefix.numeralCall J.ntag (call J.baseTag inputs))
  (seedValue J m (rootTemplate m) (rawValues J target inputs))
  (call J.childTag (.succ target ::ᵥ inputs))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram
