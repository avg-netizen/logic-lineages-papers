module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.GraphPrimitives
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof

theorem quoteGraph {arity inputs n depth ctx : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (f : Formula n) (e : FixedFormulaSubstitution.Environment n depth n) (raw : Fin n → Program inputs)
 (values : List.Vector (Term ctx) n) (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hr : ∀ i, Computes p (raw i) args (values.get i)) :
 Computes p (.composition (FixedFormulaSubstitution.formulaProgram f e) raw) args
  (FixedFormulaSubstitution.formulaValue ctag atag values f e) := by
 intro tag ht
 obtain ⟨he⟩ := Equations.compositionValues p tag _ raw ht args values
  (fun i => hr i _ (Equations.argumentChild p tag _ raw ht i))
 obtain ⟨hf⟩ := FixedFormulaSubstitution.StatementChecks.exactInternalFormula n depth n e f arity p (tag+1) ctag atag
  (Equations.functionChild p tag _ raw ht) hc ha ctx values
 exact ⟨Logic.trans _ _ _ he hf⟩

theorem headGraph {arity inputs n ctx : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (f : Formula (n+1)) (raw : Fin n → Program inputs) (values : List.Vector (Term ctx) n) (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hr : ∀ i, Computes p (raw i) args (values.get i)) :
 Computes p (headQuote f raw) args
  (FixedFormulaSubstitution.formulaValue ctag atag values f (PrescribedRuntimeSpecialization.headEnvironment n)) := by
 intro tag ht
 obtain ⟨he⟩ := Equations.compositionValues p tag _ raw ht args values
  (fun i => hr i _ (Equations.argumentChild p tag _ raw ht i))
 obtain ⟨hf⟩ := FixedFormulaSubstitution.StatementChecks.exactInternalFormula (n+1) 1 n _ f arity p (tag+1) ctag atag
  (Equations.functionChild p tag _ raw ht) hc ha ctx values
 exact ⟨Logic.trans _ _ _ he hf⟩

theorem singletonGraph {arity inputs ctx : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (ctag : Nat) (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (line : Program inputs) (v : Term ctx) (h : Computes p line args v) :
 Computes p (singleton line) args (HistoryLookup.consCall ctag v .zero) :=
 binary p args HistoryCodec.cons ctag hc line (HistoryRuleSuffix.constant inputs 0) v .zero h (constantValue p args 0)

theorem mpGraph {arity inputs ctx : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (mtag : Nat) (hm : (nodes p)[mtag]? = some ⟨4,LiteralRawMP.constructor⟩)
 (f imp ant : Program inputs) (fv iv av : Term ctx)
 (hf : Computes p f args fv) (hi : Computes p imp args iv) (ha : Computes p ant args av) :
 Computes p (mp f imp ant) args (LiteralMPRun.certificate mtag .zero fv iv av) := by
 apply CurrentRecursionAccumulator.GraphSupport.composition p args LiteralRawMP.constructor mtag hm _ (.zero ::ᵥ fv ::ᵥ iv ::ᵥ av ::ᵥ nil)
 intro i
 cases i using Fin.cases with
 | zero => exact constantValue p args 0
 | succ i => cases i using Fin.cases with
   | zero => exact hf
   | succ i => cases i using Fin.cases with
     | zero => exact hi
     | succ i => cases i using Fin.cases with
       | zero => exact ha
       | succ i => exact Fin.elim0 i

theorem allGraph {arity inputs ctx : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (ctag rtag : Nat) (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hr : (nodes p)[rtag]? = some ⟨2,UniformClosedRule13.lineConstructor⟩)
 (matrix replacement : Program inputs) (mv rv : Term ctx)
 (hm : Computes p matrix args mv) (hre : Computes p replacement args rv) :
 Computes p (allInstance matrix replacement) args (UniformClosedRule13Certificate.certificate ctag rtag mv rv) := by
 apply singletonGraph p args ctag hc _ (UniformClosedRule13.lineCall rtag mv rv)
 apply CurrentRecursionAccumulator.GraphSupport.composition p args UniformClosedRule13.lineConstructor rtag hr _ (mv ::ᵥ rv ::ᵥ nil)
 intro i
 cases i using Fin.cases with
 | zero => exact hm
 | succ i => cases i using Fin.cases with
   | zero => exact hre
   | succ i => exact Fin.elim0 i

theorem replacementGraph {arity inputs ctx : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (ctag rtag : Nat) (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hr : (nodes p)[rtag]? = some ⟨3,UniformClosedRule12.lineConstructor⟩)
 (matrix left right : Program inputs) (mv lv rv : Term ctx)
 (hm : Computes p matrix args mv) (hl : Computes p left args lv) (hre : Computes p right args rv) :
 Computes p (replacement matrix left right) args (UniformClosedRule12Certificate.certificate ctag rtag mv lv rv) := by
 apply singletonGraph p args ctag hc _ (UniformClosedRule12.lineCall rtag mv lv rv)
 apply CurrentRecursionAccumulator.GraphSupport.composition p args UniformClosedRule12.lineConstructor rtag hr _ (mv ::ᵥ lv ::ᵥ rv ::ᵥ nil)
 intro i
 cases i using Fin.cases with
 | zero => exact hm
 | succ i => cases i using Fin.cases with
   | zero => exact hl
   | succ i => cases i using Fin.cases with
     | zero => exact hre
     | succ i => exact Fin.elim0 i
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.GraphPrimitives
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.GraphPrimitives
