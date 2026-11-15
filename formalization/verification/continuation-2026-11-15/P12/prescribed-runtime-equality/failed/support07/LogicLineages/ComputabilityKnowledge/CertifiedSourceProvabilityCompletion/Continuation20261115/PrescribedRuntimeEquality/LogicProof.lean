module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.LogicProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LiteralRawMP.DispatcherSupportProof HistoryIteratorSuffix.ReconstructionProof
theorem binary {ctx : Nat} {T : Sentence → Prop} {G : List (Formula ctx)}
 (ctag atag tag : Nat) (a b c d : Term ctx)
 (ha : Hilbert.Local T ctx G (.equal a c)) (hb : Hilbert.Local T ctx G (.equal b d)) :
 Nonempty (Hilbert.Local T ctx G
  (.equal (FixedFormulaSubstitution.binaryValue ctag atag tag a b)
   (FixedFormulaSubstitution.binaryValue ctag atag tag c d))) := by
 have happ := pairCongruence (T := T) (G := G) atag a b c d ha hb
 exact ⟨pairCongruence (T := T) (G := G) ctag (Term.numeral tag)
  (HistoryAppend.appendCall atag a b) (Term.numeral tag) (HistoryAppend.appendCall atag c d)
  (.base (.logical (.reflexive (Term.numeral tag)))) happ⟩
theorem coreFormula {ctx : Nat} {T : Sentence → Prop} {G : List (Formula ctx)}
 (tag : Nat) (index fuel A B code : Term ctx)
 (hAB : Hilbert.Local T ctx G (.equal A B))
 (hcore : Hilbert.Local T ctx G (core tag index fuel A code)) :
 Nonempty (Hilbert.Local T ctx G (core tag index fuel B code)) := by
 have hd := localUnary (.add (.var 0) (.var 0)) A B hAB
 have hd' : Hilbert.Local T ctx G (.equal (.add A A) (.add B B)) := by
  simpa only [GorbowStandardInstances.instantiate,GorbowSubstitution.substitute,Fin.cases_zero] using hd
 have hcall : Hilbert.Local T ctx G
  (.equal (LiteralCheckerAcceptance.coreCall tag index fuel .zero (.add A A) code)
   (LiteralCheckerAcceptance.coreCall tag index fuel .zero (.add B B) code)) := by
  apply callCongruence (T := T) (G := G) tag
  intro i
  cases i using Fin.cases with
  | zero => exact .base (.logical (.reflexive index))
  | succ i => cases i using Fin.cases with
    | zero => exact .base (.logical (.reflexive fuel))
    | succ i => cases i using Fin.cases with
      | zero => exact .base (.logical (.reflexive (.zero : Term ctx)))
      | succ i => cases i using Fin.cases with
        | zero => exact hd'
        | succ i => cases i using Fin.cases with
          | zero => exact .base (.logical (.reflexive code))
          | succ i => exact Fin.elim0 i
 exact ⟨localTrans _ _ _ (Hilbert.Local.mp (.base (Logic.symmetryRule T _ _)) hcall) hcore⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.LogicProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.LogicProof
