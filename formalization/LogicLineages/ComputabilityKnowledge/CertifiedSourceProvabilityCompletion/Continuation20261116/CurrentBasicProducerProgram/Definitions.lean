module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open GorbowFormulaSubstitution

/-- Exactly the original three nonrecursive Program constructors. This is syntax,
not a correctness certificate or an assumed semantic property. -/
inductive Kind : Nat → Type where
 | zero : Kind 0
 | successor : Kind 1
 | projection {n : Nat} (i : Fin n) : Kind n

def evaluator : {n : Nat} → Kind n → Program n
 | _, .zero => .zero
 | _, .successor => .succ
 | _, .projection i => .projection i

def rhs : {n : Nat} → Kind n → Term n
 | _, .zero => .zero
 | _, .successor => .succ (.var 0)
 | _, .projection i => .var i

/-- Literal original open defining equation, before universal closure. -/
def rootFormula {n : Nat} (kind : Kind n) (target : Nat) : Formula n :=
 .equal (call target (argumentVariables n)) (rhs kind)

/-- Last syntax variable is a runtime tag reification slot only. The actual
source axiom is rootFormula kind target after plugging this slot, never a new
axiom universally quantifying over a free tag. -/
def rootTemplate {n : Nat} (kind : Kind n) : Formula (n+1) :=
 .equal (CurrentRecursionBaseProgram.openCall (.var (Fin.last n))
  (List.Vector.ofFn (fun i : Fin n => (Term.var i.castSucc : Term (n+1)))))
  (renameTerm Fin.castSucc (rhs kind))

/-- Concrete producer interface is target::inputs. The reused seedProgram has
exactly the original tail-first rule13 singleton/MP recursion. -/
def program {n : Nat} (kind : Kind n) : Program (n+1) :=
 CurrentRecursionBaseProgram.seedProgram n (rootTemplate kind) (CurrentRecursionBaseProgram.rootArguments n)

/-- Original explicit seed/specialization number. Zero has no specialization
steps and is precisely its single axiomLine certificate. -/
def number {n : Nat} (kind : Kind n) (target : Nat) (inputs : List.Vector Nat n) : Nat :=
 PrescribedRuntimeSpecialization.produce (rootFormula kind target)
  (fun i => Term.numeral (inputs.get i))
  (PrescribedSourceAxiomSpecialization.seed (rootFormula kind target))

abbrev Tags := CurrentRecursionBaseProgram.Tags
/-- Only genuinely used primitive nodes are required. The reused Tags record's
r12/baseTag/childTag fields are not used by the leaf recipe or asserted installed. -/
structure Installation {arity : Nat} (p : Program arity) (J : Tags) : Prop where
 hp : (nodes p)[J.ptag]? = some ⟨2,HistoryCodec.pair⟩
 hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩
 ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩
 hn : (nodes p)[J.ntag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩
 hm : (nodes p)[J.mtag]? = some ⟨4,LiteralRawMP.constructor⟩
 h13 : (nodes p)[J.r13]? = some ⟨2,UniformClosedRule13.lineConstructor⟩

def value {n ctx : Nat} (kind : Kind n) (J : Tags) (target : Term ctx)
 (inputs : List.Vector (Term ctx) n) : Term ctx :=
 CurrentRecursionBaseProgram.seedValue J n (rootTemplate kind)
  (CurrentRecursionBaseProgram.rawValues J target inputs)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram
