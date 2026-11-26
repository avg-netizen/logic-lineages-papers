module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationSource.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FixedFormulaSubstitution
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations SixSol20261113 HistoryRuleSuffix
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- A fixed template variable denotes either an in-scope bound variable or a
runtime CLOSED raw term. No runtime formula parser/evaluator is introduced. -/
abbrev Environment (n depth inputs : Nat) := Fin n → Sum (Fin depth) (Fin inputs)
def liftEnvironment {n depth inputs : Nat} (e : Environment n depth inputs) :
 Environment (n+1) (depth+1) inputs :=
 Fin.cases (.inl 0) (fun i => match e i with
  | .inl j => .inl j.succ
  | .inr j => .inr j)
def assignment {n depth inputs : Nat} (e : Environment n depth inputs)
 (u : Fin inputs → Term 0) : Fin n → Term depth := fun i => match e i with
 | .inl j => .var j
 | .inr j => GorbowFormulaSubstitution.renameTerm Fin.elim0 (u j)
def rawInputs {inputs : Nat} (u : Fin inputs → Term 0) : List.Vector Nat inputs :=
 List.Vector.ofFn (fun i => Encodable.encode (GorbowTermPrefixCode.encode (u i)))
def unary {inputs : Nat} (tag : Nat) (q : Program inputs) : Program inputs :=
 applyTwo HistoryCodec.cons (constant inputs tag) q
def binary {inputs : Nat} (tag : Nat) (q r : Program inputs) : Program inputs :=
 unary tag (applyTwo HistoryAppend.append q r)
def termProgram {n depth inputs : Nat} (e : Environment n depth inputs) : Term n → Program inputs
 | .var i => match e i with
   | .inl j => constant inputs (Encodable.encode (GorbowTermPrefixCode.encode (.var j)))
   | .inr j => .projection j
 | .zero => constant inputs (Encodable.encode ([1] : List Nat))
 | .succ t => unary 2 (termProgram e t)
 | .add t u => binary 3 (termProgram e t) (termProgram e u)
 | .mul t u => binary 4 (termProgram e t) (termProgram e u)
 | .universalFunction t => unary 5 (termProgram e t)
def formulaProgram {inputs : Nat} : {n depth : Nat} → Formula n → Environment n depth inputs → Program inputs
 | _, _, .equal t u, e => binary 0 (termProgram e t) (termProgram e u)
 | _, _, .universalRelation t, e => unary 1 (termProgram e t)
 | _, _, .agent t, e => unary 2 (termProgram e t)
 | _, _, .knowledgeAll t, e => unary 3 (termProgram e t)
 | _, _, .knowledge t u, e => binary 4 (termProgram e t) (termProgram e u)
 | _, _, .truth t, e => unary 5 (termProgram e t)
 | _, _, .neg f, e => unary 6 (formulaProgram f e)
 | _, _, .imp f g, e => binary 7 (formulaProgram f e) (formulaProgram g e)
 | _, _, .conj f g, e => binary 8 (formulaProgram f e) (formulaProgram g e)
 | _, _, .disj f g, e => binary 9 (formulaProgram f e) (formulaProgram g e)
 | _, _, .all f, e => unary 10 (formulaProgram f (liftEnvironment e))
 | _, _, .ex f, e => unary 11 (formulaProgram f (liftEnvironment e))
def unaryValue {ctx : Nat} (ctag tag : Nat) (q : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag (Term.numeral tag) q
def binaryValue {ctx : Nat} (ctag atag tag : Nat) (q r : Term ctx) : Term ctx :=
 unaryValue ctag tag (HistoryAppend.appendCall atag q r)
def termValue {n depth inputs ctx : Nat} (ctag atag : Nat) (e : Environment n depth inputs)
 (raw : List.Vector (Term ctx) inputs) : Term n → Term ctx
 | .var i => match e i with
   | .inl j => Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (.var j)))
   | .inr j => raw.get j
 | .zero => Term.numeral (Encodable.encode ([1] : List Nat))
 | .succ t => unaryValue ctag 2 (termValue ctag atag e raw t)
 | .add t u => binaryValue ctag atag 3 (termValue ctag atag e raw t) (termValue ctag atag e raw u)
 | .mul t u => binaryValue ctag atag 4 (termValue ctag atag e raw t) (termValue ctag atag e raw u)
 | .universalFunction t => unaryValue ctag 5 (termValue ctag atag e raw t)
def formulaValue {inputs ctx : Nat} (ctag atag : Nat) (raw : List.Vector (Term ctx) inputs) :
 {n depth : Nat} → Formula n → Environment n depth inputs → Term ctx
 | _, _, .equal t u, e => binaryValue ctag atag 0 (termValue ctag atag e raw t) (termValue ctag atag e raw u)
 | _, _, .universalRelation t, e => unaryValue ctag 1 (termValue ctag atag e raw t)
 | _, _, .agent t, e => unaryValue ctag 2 (termValue ctag atag e raw t)
 | _, _, .knowledgeAll t, e => unaryValue ctag 3 (termValue ctag atag e raw t)
 | _, _, .knowledge t u, e => binaryValue ctag atag 4 (termValue ctag atag e raw t) (termValue ctag atag e raw u)
 | _, _, .truth t, e => unaryValue ctag 5 (termValue ctag atag e raw t)
 | _, _, .neg f, e => unaryValue ctag 6 (formulaValue ctag atag raw f e)
 | _, _, .imp f g, e => binaryValue ctag atag 7 (formulaValue ctag atag raw f e) (formulaValue ctag atag raw g e)
 | _, _, .conj f g, e => binaryValue ctag atag 8 (formulaValue ctag atag raw f e) (formulaValue ctag atag raw g e)
 | _, _, .disj f g, e => binaryValue ctag atag 9 (formulaValue ctag atag raw f e) (formulaValue ctag atag raw g e)
 | _, _, .all f, e => unaryValue ctag 10 (formulaValue ctag atag raw f (liftEnvironment e))
 | _, _, .ex f, e => unaryValue ctag 11 (formulaValue ctag atag raw f (liftEnvironment e))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FixedFormulaSubstitution
