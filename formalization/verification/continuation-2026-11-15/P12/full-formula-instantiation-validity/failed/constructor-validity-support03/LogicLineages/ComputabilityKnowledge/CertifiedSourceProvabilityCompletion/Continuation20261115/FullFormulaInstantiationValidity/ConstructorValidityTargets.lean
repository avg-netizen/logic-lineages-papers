module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.ClosedTermDepthStatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.ConstructorValidityTargets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
open SixSol20261113 RelationalSyntaxDepthTransport.ConstructorStepTargets
/-- Literal finite concatenation: unary input is unchanged, binary is original
append. No arbitrary encoded-list decoding is used for this finite row. -/
def rawSequence {ctx : Nat} (atag : Nat) : List (Term ctx) → Term ctx
 | [] => .zero
 | [a] => a
 | a :: b :: rest => HistoryAppend.appendCall atag a (rawSequence atag (b :: rest))
def singleton {ctx : Nat} (ctag : Nat) (task : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag task .zero
/-- All six term and twelve formula constructor rows of the ORIGINAL grammar.
The sole local premises are actual closed scans of each child at its EXACT row
task (including increased binder bounds). No expansion, frame, concatenation,
step-success or scan-success transfer is supplied as a premise. -/
def InternalConstructorValidity : Prop := ∀ n (p : Program n) (stag ptag ctag atag : Nat),
 (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (G : List (Formula ctx)) (ctor : Constructor) (bound : Term ctx) (children : List (Term ctx)),
 List.Forall₂ (fun task raw => Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxScan.scanCall stag (singleton ctag task) raw) (.succ .zero))))
  (tasks ptag bound ctor) children →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxScan.scanCall stag
   (singleton ctag (LiteralSyntaxStep.taskCall ptag (kind ctor) bound))
   (HistoryLookup.consCall ctag (Term.numeral (token ctor)) (rawSequence atag children))) (.succ .zero)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.ConstructorValidityTargets
