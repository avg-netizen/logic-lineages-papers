module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLookup.DestructorProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLookup.ReferenceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph

def someTag (tag : Nat) := tag + argumentTag HistoryCodec.select referenceArguments 2
def headTag (tag : Nat) := someTag tag + argumentTag .succ (fun _ : Fin 1 => head) 0

theorem headInstalled {n : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨1,reference⟩) :
    (nodes p)[headTag tag]? = some ⟨1,head⟩ := by
  have hs := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select referenceArguments ht 2
  exact SixSol20261112.Fuel.Equations.argumentChild p (someTag tag) .succ (fun _ : Fin 1 => head) hs 0

theorem referenceEquation {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨1,reference⟩) (code : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (code ::ᵥ nil))
        (call (tag+1) (code ::ᵥ .zero ::ᵥ .succ (call (headTag tag) (code ::ᵥ nil)) ::ᵥ nil)))) := by
  let ztag := tag + argumentTag HistoryCodec.select referenceArguments 1
  have hz := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select referenceArguments ht 1
  have hzf := SixSol20261112.Fuel.Equations.functionChild p ztag Program.zero Fin.elim0 hz
  obtain ⟨hzc⟩ := SixSol20261112.Fuel.Equations.compositionValues p ztag Program.zero Fin.elim0 hz
    (code ::ᵥ nil) nil (fun i => Fin.elim0 i)
  obtain ⟨hzz⟩ := Support.intoRegistry p Program.zero (ztag+1) hzf _ (NamedArithmeticGraph.Equations.zero (ztag+1) ctx)
  have hs := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select referenceArguments ht 2
  have hsf := SixSol20261112.Fuel.Equations.functionChild p (someTag tag) .succ (fun _ : Fin 1 => head) hs
  obtain ⟨hsc⟩ := GorbowPRSymbolicEquations.Proof.compositionEquation n p (someTag tag) 1 1 .succ (fun _ : Fin 1 => head) hs ctx (code ::ᵥ nil)
  obtain ⟨hss⟩ := Support.intoRegistry p .succ (someTag tag+1) hsf _
    (NamedArithmeticGraph.Equations.successor (someTag tag+1) ctx (call (headTag tag) (code ::ᵥ nil) ::ᵥ nil))
  apply SixSol20261112.Fuel.Equations.compositionValues p tag HistoryCodec.select referenceArguments ht (code ::ᵥ nil)
    (code ::ᵥ .zero ::ᵥ .succ (call (headTag tag) (code ::ᵥ nil)) ::ᵥ nil)
  intro i
  cases i using Fin.cases with
  | zero =>
      have h := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select referenceArguments ht 0
      exact SixSol20261112.Fuel.Equations.projection p _ (0 : Fin 1) h _
  | succ i => cases i using Fin.cases with
    | zero => exact ⟨Logic.trans _ _ _ hzc hzz⟩
    | succ i => cases i using Fin.cases with
      | zero => exact ⟨Logic.trans _ _ _ hsc hss⟩
      | succ i => exact Fin.elim0 i

theorem referenceZero {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨1,reference⟩) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (call (ctx := ctx) tag (.zero ::ᵥ nil)) .zero)) := by
  have hs := SixSol20261112.Fuel.Equations.functionChild p tag HistoryCodec.select referenceArguments ht
  obtain ⟨he⟩ := referenceEquation p tag ht (.zero : Term ctx)
  obtain ⟨hz⟩ := HistoryCodec.PairProof.selectZero p (tag+1) hs .zero (.succ (call (headTag tag) (.zero ::ᵥ nil)))
  exact ⟨Logic.trans _ _ _ he hz⟩

theorem referenceCons {n ctx : Nat} (p : Program n) tag ctag
    (ht : (nodes p)[tag]? = some ⟨1,reference⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (a b : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (consCall ctag a b ::ᵥ nil)) (.succ a))) := by
  let code := consCall ctag a b
  let yes : Term ctx := .zero
  let no := Term.succ (call (headTag tag) (code ::ᵥ nil))
  let pair := call (ctag + argumentTag .succ (fun _ : Fin 1 => HistoryCodec.pair) 0) (a ::ᵥ b ::ᵥ nil)
  have hs := SixSol20261112.Fuel.Equations.functionChild p tag HistoryCodec.select referenceArguments ht
  obtain ⟨he⟩ := referenceEquation p tag ht code
  obtain ⟨hcons⟩ := HistoryCodec.PairProof.internalCons n p ctag hc ctx a b
  obtain ⟨hsel⟩ := HistoryCodec.PairProof.selectPositive p (tag+1) hs yes no pair
  obtain ⟨hh⟩ := DestructorProof.internalHeadCons n p (headTag tag) ctag (headInstalled p tag ht) hc ctx a b
  have htest := Logic.unary (call (tag+1) (.var 0 ::ᵥ liftTerm yes ::ᵥ liftTerm no ::ᵥ nil)) _ _ hcons
  simp only [Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,liftTerm,Support.shiftCancel,substitute,Fin.cases_zero] at htest
  have hsome := Logic.unary (.succ (.var 0)) _ _ hh
  exact ⟨Logic.trans _ _ _ he (Logic.trans _ _ _ htest (Logic.trans _ _ _ hsel hsome))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLookup.ReferenceProof
