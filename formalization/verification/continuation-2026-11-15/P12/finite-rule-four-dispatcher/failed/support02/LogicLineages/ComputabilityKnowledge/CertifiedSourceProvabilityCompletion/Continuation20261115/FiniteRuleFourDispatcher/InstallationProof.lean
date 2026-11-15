module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourDispatcher.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourDispatcher.InstallationProof
open GorbowPRProgram GorbowPRRegistry GorbowPRChildTags SixSol20261113
open HistoryRuleSuffix SixSol20261112.Fuel
/-- Select the actual zero-test branch child, retaining its root-global tag. -/
theorem noBranch {n : Nat} (p : Program n) (tag r : Nat) (yes no : Program 4)
 (h : (nodes p)[tag]? = some ⟨4,HistoryDispatcher.ruleSelect r yes no⟩) :
 ∃ (t : Nat), (nodes p)[t]? = some ⟨4,no⟩ := by
 let test := applyTwo equalCode HistoryDispatcher.ruleCode (constant 4 r)
 let g : Fin 3 → Program 4 := Fin.cases test (Fin.cases no (Fin.cases yes Fin.elim0))
 exact ⟨tag + argumentTag HistoryCodec.select g 1,
  Equations.argumentChild p tag HistoryCodec.select g h 1⟩
/-- Recover the branch leaf from the actual dispatcher, not the unrelated
supplied copy of the same AST. Duplicate registry tags are never equated. -/
theorem actualLeaf {n : Nat} (p : Program n) (dtag : Nat)
 (logical arithmetic : Program 1) (x : Program 3)
 (h : (nodes p)[dtag]? = some ⟨4,HistoryDispatcher.lineDispatcher
  LiteralSyntaxValidator.lineValidator logical arithmetic (SaturatedAxiomLeaf.saturated x)⟩) :
 ∃ (tag : Nat), (nodes p)[tag]? = some ⟨3,SaturatedAxiomLeaf.saturated x⟩ := by
 let rules := HistoryDispatcher.ruleDispatcher logical arithmetic (SaturatedAxiomLeaf.saturated x)
 let g : Fin 3 → Program 4 := Fin.cases
  (applyOne LiteralSyntaxValidator.lineValidator HistoryDispatcher.lineCode)
  (Fin.cases (constant 4 0) (Fin.cases rules Fin.elim0))
 have hr := Equations.argumentChild p dtag HistoryCodec.select g h 2
 obtain ⟨t1,h1⟩ := noBranch p _ 0 _ _ hr
 obtain ⟨t2,h2⟩ := noBranch p t1 1 _ _ h1
 obtain ⟨t3,h3⟩ := noBranch p t2 2 _ _ h2
 obtain ⟨t4,h4⟩ := noBranch p t3 3 _ _ h3
 let branch : Program 4 := .composition (SaturatedAxiomLeaf.saturated x) HistoryDispatcher.axiomArguments
 let g4 : Fin 3 → Program 4 := Fin.cases
  (applyTwo equalCode HistoryDispatcher.ruleCode (constant 4 4))
  (Fin.cases (constant 4 0) (Fin.cases branch Fin.elim0))
 let btag := t4 + argumentTag HistoryCodec.select g4 2
 have hb := Equations.argumentChild p t4 HistoryCodec.select g4 h4 2
 exact ⟨btag+1,Equations.functionChild p btag (SaturatedAxiomLeaf.saturated x)
  HistoryDispatcher.axiomArguments hb⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourDispatcher.InstallationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourDispatcher.InstallationProof
