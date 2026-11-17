module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.NativeValues
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.EvaluatorGraph
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.GraphValues
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof

def args {ctx : Nat} (tag offset : Nat) (value : Term ctx) := Term.numeral tag ::ᵥ Term.numeral offset ::ᵥ value ::ᵥ nil

theorem targetGraph {arity ctx : Nat} (p : Program arity) (tag offset : Nat) (value : Term ctx) :
 Computes p target (args tag offset value) (Term.numeral tag) := projection p _ 0

theorem projectionGraph {arity ctx : Nat} (p : Program arity) (tag offset : Nat) (value : Term ctx) :
 Computes p projectionTag (args tag offset value) (Term.numeral (tag+1)) :=
 CurrentRecursionStepProgram.EvaluatorGraph.successorGraph p _ target _ (targetGraph p tag offset value)

theorem firstGraph {arity ctx : Nat} (p : Program arity) (tag offset : Nat) (value : Term ctx) :
 Computes p firstTag (args tag offset value) (Term.numeral (tag+2)) :=
 CurrentRecursionStepProgram.EvaluatorGraph.shiftGraph p _ 2 target _ (targetGraph p tag offset value)

theorem secondGraph {arity ctx : Nat} (p : Program arity) (tag offset : Nat) (value : Term ctx) :
 Computes p secondTag (args tag offset value) (Term.numeral (tag+offset)) := by
 intro addr ht
 obtain ⟨he⟩ := Equations.compositionValues p addr HistoryCodec.add _ ht (args tag offset value)
  (Term.numeral tag ::ᵥ Term.numeral offset ::ᵥ nil) (fun i => by
   refine Fin.cases ?_ (fun j => ?_) i
   · exact targetGraph p tag offset value _ (Equations.argumentChild p addr _ _ ht 0)
   · have hj : j = 0 := Fin.eq_zero j
     subst j
     exact projection p (args tag offset value) 1 _ (Equations.argumentChild p addr _ _ ht 1))
 obtain ⟨hn⟩ := QuotedVerifierMP.QuotationProof.numeralCalculation p (addr+1) HistoryCodec.add
  (Equations.functionChild p addr _ _ ht) (tag ::ᵥ offset ::ᵥ nil) ctx
 rw [HistoryCodec.NativeProof.evaluateAdd,Nat.add_comm offset tag] at hn
 exact ⟨Logic.trans _ _ _ he hn⟩

theorem inputGraph {arity ctx : Nat} (p : Program arity) (K : Tags)
 (H : CurrentCallCongruenceProgram.Installation p K) (tag offset : Nat) (value : Term ctx) :
 Computes p rawInput (args tag offset value) (LiteralNumeralPrefix.numeralCall K.numeralTag value) :=
 unary p _ LiteralNumeralPrefix.numeralCode K.numeralTag H.hn input value (projection p _ 2)

theorem quoteTag {arity ctx : Nat} (p : Program arity) (K : Tags)
 (H : CurrentCallCongruenceProgram.Installation p K) (tag offset number : Nat) (value : Term ctx)
 (prog : Program 3) (hg : Computes p prog (args tag offset value) (Term.numeral number)) :
 Computes p (applyOne LiteralNumeralPrefix.numeralCode prog) (args tag offset value)
  (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (Term.numeral number : Term 0)))) := by
 intro addr ht
 obtain ⟨he⟩ := unary p _ LiteralNumeralPrefix.numeralCode K.numeralTag H.hn prog (Term.numeral number) hg addr ht
 have C := CurrentCalculationFormulaProgram.codecTags K.ctag K.atag K.numeralTag
 obtain ⟨hn⟩ := PrescribedRuntimeCallCongruence.ValueTraceProof.numeral (ctx := ctx) p C H.hn number
 exact ⟨Logic.trans _ _ _ he hn⟩

theorem tagsGraph {arity ctx : Nat} (p : Program arity) (K : Tags)
 (H : CurrentCallCongruenceProgram.Installation p K) (tag offset : Nat) (value : Term ctx) (i : Fin 4) :
 Computes p (rawTags.get i) (args tag offset value)
  (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode ((SyntaxProof.addresses tag offset).get i)))) := by
 simp only [rawTags,List.Vector.get_map]
 refine Fin.cases ?_ (fun j => ?_) i
 · exact quoteTag p K H tag offset tag value target (targetGraph p tag offset value)
 · refine Fin.cases ?_ (fun l => ?_) j
   · exact quoteTag p K H tag offset (tag+1) value projectionTag (projectionGraph p tag offset value)
   · refine Fin.cases ?_ (fun m => ?_) l
     · exact quoteTag p K H tag offset (tag+2) value firstTag (firstGraph p tag offset value)
     · have hm : m = 0 := Fin.eq_zero m
       subst m
       exact quoteTag p K H tag offset (tag+offset) value secondTag (secondGraph p tag offset value)

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.GraphValues
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.GraphValues
