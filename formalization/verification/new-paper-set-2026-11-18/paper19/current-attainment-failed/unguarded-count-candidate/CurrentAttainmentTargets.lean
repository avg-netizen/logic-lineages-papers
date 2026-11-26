module
public import LogicLineages.ControlSensitivityCurrent.CurrentAttainmentDefinitions
public import LogicLineages.StandardControlCurrent.PolicyShapeDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentAttainmentTargets

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open CurrentAttainment PolicyProgramComparisonTargets
open GroundEquivalence ExistentialPlan
open RawSourceDAG.InputCompiler (encodeInput)

def SuppliedData : Prop := ∀ (p : AdmissibleSum.Policy) (h : Unary),
  ∃ (v : OrdinalVector [] 1) (c : Nat) (a : Ordinal) (l : NONote),
    AdmissibleAssignment.assignment p h.term = some v ∧
    ParametricSourceSuccessor.denoteWith Phi (fun _ => 1) (v 0) = (c : Ordinal) ∧
    ParametricSourceSuccessor.denoteWith Phi (fun _ => 1) (v 1) = a ∧
    l.1.repr = ordinalNaturalProduct Ordinal.omega0 a ∧
    Order.IsSuccLimit l.1.repr ∧
    offset p (RawSourceDAG.encode ⟨[],.arrow .ground .ground,h⟩) = actualOrdinalNorm l.1.repr+c+1 ∧
    headCode p (RawSourceDAG.encode ⟨[],.arrow .ground .ground,h⟩) = rawNoteEncode l.1 ∧
    ∀ n, SourceAST.callValue p Phi h n = actualHeadValue l.1.repr (actualOrdinalNorm l.1.repr+c+1+n)-1

def CompletePrefix : Prop := ∀ l : NONote, Order.IsSuccLimit l.1.repr →
  ∀ q b, finitePrefix (rawNoteEncode l.1) q b = true ↔ ∃ t < b, AttainsAt l.1.repr q t

def TailSyntax : Prop := ∀ (h : Unary) c q,
  encodeInput (tailProgram h c q) = tailCode (RawSourceDAG.encode ⟨[],.arrow .ground .ground,h⟩) c q

def Full : Prop := SuppliedData ∧ CompletePrefix ∧ TailSyntax ∧
  ∀ (p : AdmissibleSum.Policy), PolicyShape.Effective p →
    Computable (run p) ∧ ∀ (h : Unary) (q : Request), 0 < q.1 → 0 < q.2.2.1 →
      ∃ (l : NONote) (program : InputNormalization.Input (List.replicate 2 Ty.ground) 0),
        headCode p (RawSourceDAG.encode ⟨[],.arrow .ground .ground,h⟩) = rawNoteEncode l.1 ∧
        ((∃ ρ, program.eval p Phi ρ Fin.elim0) ↔ Attains l.1.repr q) ∧
        run p (RawSourceDAG.encode ⟨[],.arrow .ground .ground,h⟩,q) = CurrentCompiler.expected program ∧
        let b := InputNormalization.normalize .nil program
        (Attains l.1.repr q ↔ ¬ Strict p Phi (BooleanCompiler.strictPair b).1.term
          (BooleanCompiler.strictPair b).2.term) ∧
        (Attains l.1.repr q ↔ ¬ Weak p Phi (BooleanCompiler.weakPair b).1.term
          (BooleanCompiler.weakPair b).2.term)

end LogicLineages.ControlSensitivityCurrent.CurrentAttainmentTargets
