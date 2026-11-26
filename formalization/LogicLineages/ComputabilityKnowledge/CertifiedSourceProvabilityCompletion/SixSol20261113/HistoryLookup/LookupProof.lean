module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLookup.DropProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLookup.ReferenceProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLookup.LookupProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph DropEquationsProof

def dropTag (tag : Nat) := tag + argumentTag reference (fun _ : Fin 1 => drop) 0

theorem lookupEquation {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨2,lookup⟩) (index code : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (lookupCall tag index code) (call (tag+1) (dropCall (dropTag tag) index code ::ᵥ nil)))) :=
  GorbowPRSymbolicEquations.Proof.compositionEquation n p tag 2 1 reference (fun _ : Fin 1 => drop) ht ctx (index ::ᵥ code ::ᵥ nil)

theorem internalLookupZeroCons : Targets.InternalLookupZeroCons := by
  intro n p tag ctag ht hc ctx a b
  have hd := SixSol20261112.Fuel.Equations.argumentChild p tag reference (fun _ : Fin 1 => drop) ht 0
  have hr := SixSol20261112.Fuel.Equations.functionChild p tag reference (fun _ : Fin 1 => drop) ht
  obtain ⟨he⟩ := lookupEquation p tag ht .zero (consCall ctag a b)
  obtain ⟨hz⟩ := dropZero p (dropTag tag) hd (consCall ctag a b)
  obtain ⟨hc⟩ := ReferenceProof.referenceCons p (tag+1) ctag hr hc a b
  exact ⟨Logic.trans _ _ _ he (Logic.trans _ _ _ (DestructorProof.unaryCallCongruence (tag+1) _ _ hz) hc)⟩

theorem internalLookupSuccessorCons : Targets.InternalLookupSuccessorCons := by
  intro n p tag ctag ht hc ctx index a b
  have hd := SixSol20261112.Fuel.Equations.argumentChild p tag reference (fun _ : Fin 1 => drop) ht 0
  obtain ⟨hl⟩ := lookupEquation p tag ht (.succ index) (consCall ctag a b)
  obtain ⟨hr⟩ := lookupEquation p tag ht index b
  obtain ⟨hc⟩ := DropProof.dropCons p (dropTag tag) ctag hd hc index a b
  exact ⟨Logic.trans _ _ _ hl (Logic.trans _ _ _
    (DestructorProof.unaryCallCongruence (tag+1) _ _ hc) (Support.equalitySymmetry _ _ hr))⟩

theorem internalLookupNil : Targets.InternalLookupNil := by
  intro n p tag ht ctx index
  have hd := SixSol20261112.Fuel.Equations.argumentChild p tag reference (fun _ : Fin 1 => drop) ht 0
  have hr := SixSol20261112.Fuel.Equations.functionChild p tag reference (fun _ : Fin 1 => drop) ht
  obtain ⟨he⟩ := lookupEquation p tag ht index .zero
  obtain ⟨hz⟩ := DropProof.dropNil p (dropTag tag) hd index
  obtain ⟨hrz⟩ := ReferenceProof.referenceZero (ctx := ctx) p (tag+1) hr
  exact ⟨Logic.trans _ _ _ he (Logic.trans _ _ _ (DestructorProof.unaryCallCongruence (tag+1) _ _ hz) hrz)⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLookup.LookupProof
