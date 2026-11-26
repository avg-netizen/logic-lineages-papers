module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceSelectorClassification.ComparatorGate
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceSelectorClassification.LogicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceSelectorClassification.ConsumerProof
open GorbowSyntax GorbowTheoryProof
open GorbowPRProgram GorbowPublishedDCB
open GorbowSortedSyntaxCode
theorem classification (pF pR : Program 1) (q : Program 5) (c : Code) (tag : Nat)
 (hA : Actual pF pR q c) (A : Selector)
 (hCollapse : Nonempty (Derivation (D pF pR q c)
  (GorbowBooleanTruth.biconditional (sourceC tag A) (everyone A (formulaCode falseEquality))))) :
 Nonempty (GorbowPublishedKT.Proof false pF pR q c
  (GorbowBooleanTruth.biconditional (selectorTheta A) (selectedNonempty A))) ∧
 Nonempty (GorbowPublishedKT.Proof false pF pR q c
  (GorbowBooleanTruth.biconditional (sourceC tag A) (.neg (selectedNonempty A)))) := by
 let T := GorbowPublishedKT.Axiom false pF pR q c
 obtain ⟨hfirst⟩ := SelectorStatementChecks.firstSelector pF pR q c hA A
 obtain ⟨hnb⟩ := GorbowPRNegativeNumerals.Proof.unequalNumerals T 0 1 (by decide)
 obtain ⟨hEN⟩ := LogicProof.complement T (everyone A (formulaCode falseEquality))
  (selectedNonempty A) falseEquality hnb hfirst
 obtain ⟨hc⟩ := GorbowTheoryProofProof.monotonicity (D pF pR q c) T
  (fun s hs => GorbowPublishedKT.Axiom.d s hs) 0 _ hCollapse
 obtain ⟨hsecond⟩ := LogicProof.chain T (sourceC tag A) (everyone A (formulaCode falseEquality))
  (.neg (selectedNonempty A)) hc hEN
 exact ⟨⟨.ordinary hfirst⟩,⟨.ordinary hsecond⟩⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceSelectorClassification.ConsumerProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceSelectorClassification.ConsumerProof
