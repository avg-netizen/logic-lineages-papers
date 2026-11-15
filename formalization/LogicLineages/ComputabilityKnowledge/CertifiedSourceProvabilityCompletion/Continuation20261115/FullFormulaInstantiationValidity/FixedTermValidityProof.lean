module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.FixedTermValidityTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.FixedTermValidityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open RelationalSyntaxDepthTransport ConstructorValidityTargets FixedFormulaSubstitution
/-- Structural validity of the original capture-correct term encoding. Runtime
inputs need actual closed-validator derivations, not native syntax witnesses. -/
theorem fixedTermValidity : FixedTermValidityTargets.InternalFixedTermValidity := by
 intro n depth inputs e t arity p vtag stag ptag ctag atag hv hs hp hc ha ctx G raw hraw
 induction t with
 | var i =>
  cases he : e i with
  | inl j =>
   obtain ⟨hj⟩ := BoundVariableValidityProof.boundVariableValidity depth j arity p stag ptag ctag atag hs hp hc ha ctx
   simpa only [termValue, he] using (show Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G _) from ⟨.base hj⟩)
  | inr j =>
   obtain ⟨hj⟩ := hraw j
   obtain ⟨hd⟩ := ClosedTermDepthProof.closedTermAtAnyDepth arity p vtag stag ptag ctag atag hv hs hp hc ha ctx (Term.numeral depth) (raw.get j)
   simpa only [termValue, he] using (show Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G _) from ⟨Hilbert.Local.mp (Hilbert.Local.base hd) hj⟩)
 | zero =>
  obtain ⟨hz⟩ := ConstructorValidityProof.constructorValidity arity p stag ptag ctag atag hs hp hc ha ctx G (.term 1) (Term.numeral depth) [] .nil
  obtain ⟨hcode⟩ := BoundVariableArithmeticProof.numeralCons (ctx := ctx) p ctag hc 1 []
  have hscan := Logic.callCongruence (ctx := ctx) (GorbowPRNumeralCalculation.Theory p) stag
   (ClosedTermDepthTargets.tasks ptag ctag (Term.numeral depth) ::ᵥ HistoryLookup.consCall ctag (Term.numeral 1) .zero ::ᵥ nil)
   (ClosedTermDepthTargets.tasks ptag ctag (Term.numeral depth) ::ᵥ Term.numeral (Encodable.encode ([1] : List Nat)) ::ᵥ nil) (fun i => by
    cases i using Fin.cases with
    | zero => exact .logical (.reflexive _)
    | succ i => cases i using Fin.cases with
      | zero => exact hcode
      | succ i => exact Fin.elim0 i)
  exact ⟨localTrans _ _ _ (.base (Support.equalitySymmetry _ _ hscan)) hz⟩
 | succ t ih =>
  have hchildren : List.Forall₂ (fun task value => Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (.equal (LiteralSyntaxScan.scanCall stag (singleton ctag task) value) (.succ .zero))))
   (ConstructorStepTargets.tasks ptag (Term.numeral depth) (.term 2)) [termValue ctag atag e raw t] :=
   .cons ih .nil
  obtain ⟨hcoded⟩ := ConstructorValidityProof.constructorValidity arity p stag ptag ctag atag hs hp hc ha ctx G
   (.term 2) (Term.numeral depth) [termValue ctag atag e raw t] hchildren
  exact ⟨hcoded⟩
 | add t u iht ihu =>
  have hchildren : List.Forall₂ (fun task value => Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (.equal (LiteralSyntaxScan.scanCall stag (singleton ctag task) value) (.succ .zero))))
   (ConstructorStepTargets.tasks ptag (Term.numeral depth) (.term 3)) [termValue ctag atag e raw t, termValue ctag atag e raw u] :=
   .cons iht (.cons ihu .nil)
  obtain ⟨hcoded⟩ := ConstructorValidityProof.constructorValidity arity p stag ptag ctag atag hs hp hc ha ctx G
   (.term 3) (Term.numeral depth) [termValue ctag atag e raw t, termValue ctag atag e raw u] hchildren
  exact ⟨hcoded⟩
 | mul t u iht ihu =>
  have hchildren : List.Forall₂ (fun task value => Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (.equal (LiteralSyntaxScan.scanCall stag (singleton ctag task) value) (.succ .zero))))
   (ConstructorStepTargets.tasks ptag (Term.numeral depth) (.term 4)) [termValue ctag atag e raw t, termValue ctag atag e raw u] :=
   .cons iht (.cons ihu .nil)
  obtain ⟨hcoded⟩ := ConstructorValidityProof.constructorValidity arity p stag ptag ctag atag hs hp hc ha ctx G
   (.term 4) (Term.numeral depth) [termValue ctag atag e raw t, termValue ctag atag e raw u] hchildren
  exact ⟨hcoded⟩
 | universalFunction t ih =>
  have hchildren : List.Forall₂ (fun task value => Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (.equal (LiteralSyntaxScan.scanCall stag (singleton ctag task) value) (.succ .zero))))
   (ConstructorStepTargets.tasks ptag (Term.numeral depth) (.term 5)) [termValue ctag atag e raw t] :=
   .cons ih .nil
  obtain ⟨hcoded⟩ := ConstructorValidityProof.constructorValidity arity p stag ptag ctag atag hs hp hc ha ctx G
   (.term 5) (Term.numeral depth) [termValue ctag atag e raw t] hchildren
  exact ⟨hcoded⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.FixedTermValidityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.FixedTermValidityProof
