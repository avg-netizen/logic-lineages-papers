module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.TableGapProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.AppendEquationsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph TableEquationsProof TableLookupProof

def tableTag (tag : Nat) := tag + argumentTag HistoryLookup.head (fun _ : Fin 1 => table) 0

theorem tableInstalled {n : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨2,append⟩) :
    (nodes p)[tableTag tag]? = some ⟨2,table⟩ :=
  SixSol20261112.Fuel.Equations.argumentChild p tag HistoryLookup.head (fun _ : Fin 1 => table) ht 0

theorem headInstalled {n : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨2,append⟩) :
    (nodes p)[tag+1]? = some ⟨1,HistoryLookup.head⟩ :=
  SixSol20261112.Fuel.Equations.functionChild p tag HistoryLookup.head (fun _ : Fin 1 => table) ht

theorem appendEquation {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨2,append⟩) (left right : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (appendCall tag left right) (headCall (tag+1) (tableCall (tableTag tag) left right)))) :=
  GorbowPRSymbolicEquations.Proof.compositionEquation n p tag 2 1 HistoryLookup.head (fun _ : Fin 1 => table) ht ctx (left ::ᵥ right ::ᵥ nil)

theorem internalAppendNil : Targets.InternalAppendNil := by
  intro n p tag ht ctx right
  have htab := tableInstalled p tag ht
  obtain ⟨he⟩ := appendEquation p tag ht .zero right
  obtain ⟨hz⟩ := tableZero p (tableTag tag) htab right
  obtain ⟨hh⟩ := HistoryLookup.DestructorProof.internalHeadCons n p (tag+1) (consTag (tableTag tag))
    (headInstalled p tag ht) (consInstalled p (tableTag tag) htab) ctx right .zero
  exact ⟨Logic.trans _ _ _ he (Logic.trans _ _ _ (HistoryLookup.DestructorProof.unaryCallCongruence (tag+1) _ _ hz) hh)⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.AppendEquationsProof
