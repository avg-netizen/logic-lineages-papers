module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.SymbolicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.RootEncodingProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence CurrentImplicationCertificate CurrentEqualityImplication
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open FixedFormulaSubstitution GorbowPRDefiningEquations

theorem root {arity k m ctx : Nat} (p : Program arity) (installed : Formula 1)
 (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a x)
 (f : Program m) (tag : Nat) (counter : Term ctx) (raw : List.Vector (Term ctx) m) :
 let J := tags I.previous
 let counterRaw := LiteralNumeralPrefix.numeralCall J.numeralTag counter
 let priorCall := callValue J (Term.numeral tag) (counterRaw ::ᵥ raw)
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (PrescribedRuntimeSpecialization.value I.previous.previous.current.ctag I.previous.previous.current.atag
   (rootFormula f tag) (counterRaw ::ᵥ raw))
   (equalValue J.ctag J.atag
    (callValue J (Term.numeral tag) (LiteralNumeralPrefix.numeralCall J.numeralTag (.succ counter) ::ᵥ raw))
    (callValue J (Term.numeral (tag+GorbowPRChildTags.stepTag f)) (counterRaw ::ᵥ priorCall ::ᵥ raw))))) := by
 dsimp only
 let J := tags I.previous
 let e := PrescribedRuntimeSpecialization.runtimeEnvironment (m+1)
 let counterRaw := LiteralNumeralPrefix.numeralCall J.numeralTag counter
 let values := counterRaw ::ᵥ raw
 let oldCall := call tag (.var 0 ::ᵥ tailVariables m)
 let priorCall := callValue J (Term.numeral tag) values
 have hc := I.previous.current.h_ctag
 have ha := I.previous.current.h_atag
 have hn := I.previous.previous.previous.previous.previous.hnumeral
 obtain ⟨hcopy⟩ := CurrentCompositionCertificate.TermCopiesProof.equalFormula p
  I.previous.previous.current.ctag I.previous.previous.current.atag J.ctag J.atag
  I.previous.previous.current.h_ctag I.previous.previous.current.h_atag hc ha e values
  (call tag (.succ (.var 0) ::ᵥ tailVariables m))
  (call (tag+GorbowPRChildTags.stepTag f) (.var 0 ::ᵥ oldCall ::ᵥ tailVariables m))
 obtain ⟨hprior⟩ := CurrentCompositionCertificate.CallEncodingProof.call p J hc ha hn e values tag (.var 0 ::ᵥ tailVariables m)
 have hmap : (.var 0 ::ᵥ tailVariables m).map (termValue J.ctag J.atag e values) = values := by
  rw [List.Vector.map_cons,SymbolicProof.runtimeTail]
  rfl
 rw [hmap] at hprior
 obtain ⟨hleft⟩ := CurrentCompositionCertificate.CallEncodingProof.call p J hc ha hn e values tag (.succ (.var 0) ::ᵥ tailVariables m)
 obtain ⟨hsucc⟩ := LiteralNumeralPrefix.EquationsProof.successor p J.numeralTag J.ctag hn hc counter
 have hleftArgs : ∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (((.succ (.var 0) ::ᵥ tailVariables m).map (termValue J.ctag J.atag e values)).get i)
   ((LiteralNumeralPrefix.numeralCall J.numeralTag (.succ counter) ::ᵥ raw).get i))) := by
  intro i
  cases i using Fin.cases with
  | zero => exact ⟨Support.equalitySymmetry _ _ hsucc⟩
  | succ i =>
   simp only [List.Vector.map_cons,List.Vector.get_cons_succ]
   rw [SymbolicProof.runtimeTail]
   exact ⟨.logical (.reflexive _)⟩
 obtain ⟨hlArgs⟩ := CurrentCompositionCertificate.ValueCongruenceProof.calls p J hc ha (Term.numeral tag) _ _ hleftArgs
 have hl := Logic.trans _ _ _ hleft hlArgs
 obtain ⟨hright⟩ := CurrentCompositionCertificate.CallEncodingProof.call p J hc ha hn e values
  (tag+GorbowPRChildTags.stepTag f) (.var 0 ::ᵥ oldCall ::ᵥ tailVariables m)
 have hrightArgs : ∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (((.var 0 ::ᵥ oldCall ::ᵥ tailVariables m).map (termValue J.ctag J.atag e values)).get i)
   ((counterRaw ::ᵥ priorCall ::ᵥ raw).get i))) := by
  intro i
  cases i using Fin.cases with
  | zero => exact ⟨.logical (.reflexive _)⟩
  | succ i => cases i using Fin.cases with
    | zero => exact ⟨hprior⟩
    | succ i =>
     simp only [List.Vector.map_cons,List.Vector.get_cons_succ]
     rw [SymbolicProof.runtimeTail]
     exact ⟨.logical (.reflexive _)⟩
 obtain ⟨hrArgs⟩ := CurrentCompositionCertificate.ValueCongruenceProof.calls p J hc ha
  (Term.numeral (tag+GorbowPRChildTags.stepTag f)) _ _ hrightArgs
 have hr := Logic.trans _ _ _ hright hrArgs
 obtain ⟨heq⟩ := CurrentCompositionCertificate.CodecProof.binary p J.ctag J.atag J.ctag J.atag 0 hc ha hc ha _ _ _ _ hl hr
 exact ⟨Logic.trans _ _ _ hcopy heq⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.RootEncodingProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.RootEncodingProof
