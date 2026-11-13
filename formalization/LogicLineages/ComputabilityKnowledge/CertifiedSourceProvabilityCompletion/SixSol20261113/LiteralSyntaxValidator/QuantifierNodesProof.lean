module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.QuantifierOperationalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.QuantifierNodesProof
open GorbowPRProgram GorbowPRRegistry GorbowPRChildTags HistoryRuleSuffix LiteralSyntaxStep
open SixSol20261112.Fuel

theorem appendInstalled {n : Nat} (p : Program n) (stag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,stepCode⟩) :
 ∃ atag : Nat, (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ := by
 let inner := choose expanded (constant 2 0) (success appended)
 let middle := choose stack (constant 2 0) inner
 let g1 : Fin 3 → Program 2 := Fin.cases (.projection 0) (Fin.cases (constant 2 0) (Fin.cases middle Fin.elim0))
 let t1 := stag+argumentTag HistoryCodec.select g1 2
 have h1 := Equations.argumentChild p stag HistoryCodec.select g1 hs 2
 let g2 : Fin 3 → Program 2 := Fin.cases stack (Fin.cases (constant 2 0) (Fin.cases inner Fin.elim0))
 let t2 := t1+argumentTag HistoryCodec.select g2 2
 have h2 := Equations.argumentChild p t1 HistoryCodec.select g2 h1 2
 let g3 : Fin 3 → Program 2 := Fin.cases expanded (Fin.cases (constant 2 0) (Fin.cases (success appended) Fin.elim0))
 let t3 := t2+argumentTag HistoryCodec.select g3 2
 have h3 := Equations.argumentChild p t2 HistoryCodec.select g3 h2 2
 let t4 := t3+argumentTag .succ (fun _ : Fin 1 => appended) 0
 have h4 := Equations.argumentChild p t3 .succ (fun _ : Fin 1 => appended) h3 0
 exact ⟨t4+1,Equations.functionChild p t4 HistoryAppend.append
  (Fin.cases (applyOne HistoryCodec.predecessor expanded) (Fin.cases restTasks Fin.elim0)) h4⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.QuantifierNodesProof

#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.QuantifierNodesProof
