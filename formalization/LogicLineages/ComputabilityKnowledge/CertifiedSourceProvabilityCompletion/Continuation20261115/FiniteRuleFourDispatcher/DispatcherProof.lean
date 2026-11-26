module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourDispatcher.NumericProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourDispatcher.DispatcherProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open HistoryRuleSuffix SixSol20261112.Fuel NamedArithmeticGraph
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open RawEqualityInstantiationDispatcher.DispatcherProof
/-- Original equalCode on literal 4 and a fixed rule index. -/
theorem ruleTest {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (sigma : Sentence) (index fuel history : Term ctx) (r : Nat) :
 Computes p G (applyTwo equalCode HistoryDispatcher.ruleCode (constant 4 r))
  (index ::ᵥ fuel ::ᵥ history ::ᵥ Term.numeral (FiniteRuleFourLeaf.lineCode sigma) ::ᵥ nil)
  (Term.numeral (if 4=r then 1 else 0)) := by
 let args := index ::ᵥ fuel ::ᵥ history ::ᵥ Term.numeral (FiniteRuleFourLeaf.lineCode sigma) ::ᵥ nil
 apply binary p G args equalCode _ _ (Term.numeral 4) (Term.numeral r) _
  (NumericProof.ruleFour p G sigma index fuel history) (constantValue p G args r)
 have hn := NumericProof.numerals p G equalCode (4 ::ᵥ r ::ᵥ nil)
 simpa only [HistoryRuleSuffix.NativeProof.equalEval,List.Vector.map_cons,List.Vector.map_nil] using hn
/-- Internal conditional composition lemma only. The final theorem supplies
and discharges its leaf-success premise from the actual finite source proof. -/
theorem fromLeaf {n ctx : Nat} (p : Program n) (dtag xtag : Nat)
 (logical arithmetic : Program 1) (x : Program 3)
 (hd : (nodes p)[dtag]? = some ⟨4,HistoryDispatcher.lineDispatcher
  LiteralSyntaxValidator.lineValidator logical arithmetic (SaturatedAxiomLeaf.saturated x)⟩)
 (hx : (nodes p)[xtag]? = some ⟨3,SaturatedAxiomLeaf.saturated x⟩)
 (sigma : Sentence) (index fuel history : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (SaturatedAxiomLeaf.success xtag index fuel (Term.numeral (FiniteRuleFourLeaf.lineCode sigma)))
   (.equal (HistoryDispatcher.dispatcherCall dtag index fuel history
    (Term.numeral (FiniteRuleFourLeaf.lineCode sigma))) (.succ .zero)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let line : Term ctx := Term.numeral (FiniteRuleFourLeaf.lineCode sigma)
 let H := SaturatedAxiomLeaf.success xtag index fuel line
 let G := [H]
 let args := index ::ᵥ fuel ::ᵥ history ::ᵥ line ::ᵥ nil
 have hh : Hilbert.Local T ctx G H := .hypothesis List.mem_cons_self
 have hleaf : Computes p G (SaturatedAxiomLeaf.saturated x) (index ::ᵥ fuel ::ᵥ line ::ᵥ nil) (.succ .zero) :=
  valueAt p G (SaturatedAxiomLeaf.saturated x) xtag hx _ _ hh
 have hax : Computes p G (.composition (SaturatedAxiomLeaf.saturated x) HistoryDispatcher.axiomArguments) args (.succ .zero) := by
  apply compose p G _ _ args (index ::ᵥ fuel ::ᵥ line ::ᵥ nil) _ _ hleaf
  intro i
  cases i using Fin.cases with
  | zero => exact projection p G args 0
  | succ i => cases i using Fin.cases with
    | zero => exact projection p G args 1
    | succ i => cases i using Fin.cases with
      | zero => exact projection p G args 3
      | succ i => exact Fin.elim0 i
 have ht0 : Computes p G (applyTwo equalCode HistoryDispatcher.ruleCode (constant 4 0)) args .zero := by
  simpa only [show (4=0) = False from propext (by decide),ite_false,Term.numeral] using ruleTest p G sigma index fuel history 0
 have ht1 : Computes p G (applyTwo equalCode HistoryDispatcher.ruleCode (constant 4 1)) args .zero := by
  simpa only [show (4=1) = False from propext (by decide),ite_false,Term.numeral] using ruleTest p G sigma index fuel history 1
 have ht2 : Computes p G (applyTwo equalCode HistoryDispatcher.ruleCode (constant 4 2)) args .zero := by
  simpa only [show (4=2) = False from propext (by decide),ite_false,Term.numeral] using ruleTest p G sigma index fuel history 2
 have ht3 : Computes p G (applyTwo equalCode HistoryDispatcher.ruleCode (constant 4 3)) args .zero := by
  simpa only [show (4=3) = False from propext (by decide),ite_false,Term.numeral] using ruleTest p G sigma index fuel history 3
 have ht4 : Computes p G (applyTwo equalCode HistoryDispatcher.ruleCode (constant 4 4)) args (.succ .zero) := by
  simpa only [ite_true,Term.numeral] using ruleTest p G sigma index fuel history 4
 have h4 := choosePositive p G args _ (constant 4 0) _ .zero (.succ .zero) ht4 hax
 have h3 := chooseZero p G args _ _ HistoryDispatcher.generalizeBranch (.succ .zero) ht3 h4
 have h2 := chooseZero p G args _ _ HistoryDispatcher.mpBranch (.succ .zero) ht2 h3
 have h1 := chooseZero p G args _ _ (applyOne arithmetic HistoryDispatcher.lineCode) (.succ .zero) ht1 h2
 have h0 := chooseZero p G args _ _ (applyOne logical HistoryDispatcher.lineCode) (.succ .zero) ht0 h1
 have hv : Computes p G LiteralSyntaxValidator.lineValidator (line ::ᵥ nil) (.succ .zero) := by
  have hn := NumericProof.numerals p G LiteralSyntaxValidator.lineValidator (FiniteRuleFourLeaf.lineCode sigma ::ᵥ nil)
  simpa only [NumericProof.validCanonical,List.Vector.map_cons,List.Vector.map_nil,Term.numeral] using hn
 have hl : Computes p G HistoryDispatcher.lineCode args line := projection p G args 3
 have hvalid := unary p G args LiteralSyntaxValidator.lineValidator HistoryDispatcher.lineCode line (.succ .zero) hl hv
 obtain ⟨hout⟩ := choosePositive p G args _ (constant 4 0) _ .zero (.succ .zero) hvalid h0 dtag hd
 exact ⟨hout.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourDispatcher.DispatcherProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourDispatcher.DispatcherProof
