module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.BoundVariableValidityTargets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.QuotedVerifierMP.QuotationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.BoundVariableArithmeticProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph
/-- Concrete fixed-index gap is realized by original PA numeral addition and
actual difference cancellation, not by validator evaluation or reflection. -/
theorem positiveDifference (depth : Nat) (index : Fin depth) {n ctx : Nat} (p : Program n) (dtag : Nat)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩) :
 ∃ gap : Nat, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (HistoryDifference.differenceCall dtag (Term.numeral (n := ctx) index.val) (Term.numeral depth))
   (.succ (Term.numeral gap)))) := by
 let gap := depth - index.val - 1
 have hgap : index.val + Nat.succ gap = depth := by have hi := index.isLt; dsimp [gap]; omega
 obtain ⟨hadd⟩ := QuotedVerifierMP.QuotationProof.numeralAdd (GorbowPRNumeralCalculation.Theory p) ctx index.val (Nat.succ gap)
 rw [hgap] at hadd
 obtain ⟨hcancel⟩ := HistoryDifference.ArithmeticProof.differenceCancel n p dtag hd ctx
  (Term.numeral index.val) (.succ (Term.numeral gap))
 have hc := Logic.callCongruence (GorbowPRNumeralCalculation.Theory p) dtag
  (Term.numeral index.val ::ᵥ Term.numeral depth ::ᵥ nil)
  (Term.numeral index.val ::ᵥ .add (Term.numeral index.val) (.succ (Term.numeral gap)) ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact .logical (.reflexive _)
   | succ i => cases i using Fin.cases with
     | zero => exact Support.equalitySymmetry _ _ hadd
     | succ i => exact Fin.elim0 i)
 exact ⟨gap,⟨Logic.trans _ _ _ hc hcancel⟩⟩
/-- Only concrete list-code arithmetic is calculated: the primitive-recursive
numeral calculation theorem expands actual defining equations, not syntax validity. -/
theorem numeralCons {n ctx : Nat} (p : Program n) (ctag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (a : Nat) (xs : List Nat) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (HistoryLookup.consCall ctag (Term.numeral (n := ctx) a) (Term.numeral (Encodable.encode xs)))
   (Term.numeral (Encodable.encode (a :: xs))))) := by
 obtain ⟨h⟩ := QuotedVerifierMP.QuotationProof.numeralCalculation p ctag HistoryCodec.cons hc
  (a ::ᵥ Encodable.encode xs ::ᵥ nil) ctx
 rw [HistoryCodec.NativeProof.nativeConsAllVectors] at h
 simpa only [HistoryLookup.consCall,HistoryLookup.NativeProof.encodeCons,List.Vector.map_cons,List.Vector.map_nil,
  List.Vector.head_cons,List.Vector.tail_cons] using (show Nonempty _ from ⟨h⟩)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.BoundVariableArithmeticProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.BoundVariableArithmeticProof
