module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.FixedTermValidityStatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.FixedFormulaValidityTargets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
open SixSol20261113 FixedFormulaSubstitution
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Original full formulaValue at every capture-correct bound/runtime environment.
All twelve original constructors, including liftEnvironment under both binders.
Every runtime coordinate has an actual closed-term validator proof; no native
image, validity-reflection, or externally supplied constructor closure premise. -/
def InternalFixedFormulaValidity : Prop := ∀ n depth inputs (e : Environment n depth inputs) (f : Formula n)
 arity (p : Program arity) (vtag stag ptag ctag atag : Nat),
 (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩ →
 (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (G : List (Formula ctx)) (raw : List.Vector (Term ctx) inputs),
 (∀ i : Fin inputs, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid vtag (raw.get i)))) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxScan.scanCall stag
   (ConstructorValidityTargets.singleton ctag (LiteralSyntaxStep.taskCall ptag 1 (Term.numeral depth)))
    (FixedFormulaSubstitution.formulaValue ctag atag raw f e)) (.succ .zero)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.FixedFormulaValidityTargets
