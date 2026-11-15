module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.ConstructorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.StackProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph RelationalSyntaxDepthTransport
/-- Original ordered finite pending tasks, with an arbitrary symbolic rest. -/
def prepend {ctx : Nat} (ctag : Nat) : List (Term ctx) → Term ctx → Term ctx
 | [], rest => rest
 | x::xs, rest => HistoryLookup.consCall ctag x (prepend ctag xs rest)
/-- Expand the actual append of a literal finite task row; no claim about
native-list images of the symbolic rest is used. -/
theorem appendPrefix {n ctx : Nat} (p : Program n) (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (xs : List (Term ctx)) (rest : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (HistoryAppend.appendCall atag (FinitePrefixTargets.prefixTerm ctag xs) rest)
   (prepend ctag xs rest))) := by
 induction xs with
 | nil => exact HistoryAppend.AppendEquationsProof.internalAppendNil n p atag ha ctx rest
 | cons x xs ih =>
  obtain ⟨hi⟩ := ih
  obtain ⟨hcons⟩ := HistoryAppend.ConsProof.internalAppendCons n p atag ctag ha hc ctx
   x (FinitePrefixTargets.prefixTerm ctag xs) rest
  have htail := Logic.callCongruence (GorbowPRNumeralCalculation.Theory p) ctag
   (x ::ᵥ HistoryAppend.appendCall atag (FinitePrefixTargets.prefixTerm ctag xs) rest ::ᵥ nil)
   (x ::ᵥ prepend ctag xs rest ::ᵥ nil) (fun i => by
    cases i using Fin.cases with
    | zero => exact .logical (.reflexive _)
    | succ i => cases i using Fin.cases with
      | zero => exact hi
      | succ i => exact Fin.elim0 i)
  exact ⟨Logic.trans _ _ _ hcons htail⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.StackProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.StackProof
