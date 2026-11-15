module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.TaskProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.FinitePrefixProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.RowProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open RelationalSyntaxDepthTransport.ConstructorStepTargets
/-- The marker0 emits no token, so its new pending task remains the whole term.
Every other row is the actual original constructor expansion at the new depth. -/
def newRows {ctx : Nat} (ptag : Nat) (binder : Term ctx) : Constructor → List (Term ctx)
 | .term i =>
  match i.val with
  | 0 => [LiteralSyntaxStep.taskCall ptag 0 binder]
  | 1 => []
  | 2 => [LiteralSyntaxStep.taskCall ptag 0 binder]
  | 3 => [LiteralSyntaxStep.taskCall ptag 0 binder, LiteralSyntaxStep.taskCall ptag 0 binder]
  | 4 => [LiteralSyntaxStep.taskCall ptag 0 binder, LiteralSyntaxStep.taskCall ptag 0 binder]
  | _ => [LiteralSyntaxStep.taskCall ptag 0 binder]
 | .formula i =>
  match i.val with
  | 0 => [LiteralSyntaxStep.taskCall ptag 0 binder, LiteralSyntaxStep.taskCall ptag 0 binder]
  | 1 => [LiteralSyntaxStep.taskCall ptag 0 binder]
  | 2 => [LiteralSyntaxStep.taskCall ptag 0 binder]
  | 3 => [LiteralSyntaxStep.taskCall ptag 0 binder]
  | 4 => [LiteralSyntaxStep.taskCall ptag 0 binder, LiteralSyntaxStep.taskCall ptag 0 binder]
  | 5 => [LiteralSyntaxStep.taskCall ptag 0 binder]
  | 6 => [LiteralSyntaxStep.taskCall ptag 1 binder]
  | 7 => [LiteralSyntaxStep.taskCall ptag 1 binder, LiteralSyntaxStep.taskCall ptag 1 binder]
  | 8 => [LiteralSyntaxStep.taskCall ptag 1 binder, LiteralSyntaxStep.taskCall ptag 1 binder]
  | 9 => [LiteralSyntaxStep.taskCall ptag 1 binder, LiteralSyntaxStep.taskCall ptag 1 binder]
  | _ => [LiteralSyntaxStep.taskCall ptag 1 (.succ binder)]

theorem rows {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ptag l r : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (ctor : Constructor) (depth : Term ctx) :
 List.Forall₂ (fun x y => Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (taskRelation l r x y))) (tasks ptag (.succ depth) ctor) (newRows ptag depth ctor) := by
 obtain ⟨h0⟩ := TaskProof.term p G ptag l r hp hl hr depth
 obtain ⟨h1⟩ := TaskProof.formula p G ptag l r hp hl hr depth
 obtain ⟨h2⟩ := TaskProof.index p G ptag l r hp hl hr depth
 obtain ⟨hs⟩ := TaskProof.formula p G ptag l r hp hl hr (.succ depth)
 cases ctor with
 | term i =>
  simp only [tasks,newRows]
  split <;> first
   | exact .nil
   | exact .cons ⟨h0⟩ .nil
   | exact .cons ⟨h2⟩ .nil
   | exact .cons ⟨h0⟩ (.cons ⟨h0⟩ .nil)
 | formula i =>
  simp only [tasks,newRows]
  split <;> first
   | exact .cons ⟨h0⟩ .nil
   | exact .cons ⟨h1⟩ .nil
   | exact .cons ⟨hs⟩ .nil
   | exact .cons ⟨h0⟩ (.cons ⟨h0⟩ .nil)
   | exact .cons ⟨h1⟩ (.cons ⟨h1⟩ .nil)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.RowProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.RowProof
