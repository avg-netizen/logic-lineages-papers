module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.EnvironmentProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.FixedTemplateEncodingStatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.BaseProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof
theorem emptyValue {arity ctx : Nat} (p : Program arity) (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (f : Formula 0) (raw : List.Vector (Term ctx) 0) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (value ctag atag f raw) (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode f))))) := by
 rw [List.Vector.eq_nil raw]
 have he : runtimeEnvironment 0 = FullFormulaInstantiationValidity.FixedTemplateEncodingTargets.boundEnvironment 0 := by
  funext i
  exact Fin.elim0 i
 unfold value
 rw [he]
 exact FullFormulaInstantiationValidity.FixedTemplateEncodingStatementChecks.exactBoundFormulaEncoding
  0 f arity p ctag atag hc ha ctx
/-- Formula-code equality transports actual CORE calls, with all other inputs fixed. -/
theorem coreTransport {ctx : Nat} (T : Sentence → Prop) (G : List (Formula ctx))
 (tag : Nat) (index fuel a b code : Term ctx)
 (hab : Hilbert.Local T ctx G (.equal a b))
 (ha : Hilbert.Local T ctx G
  (.equal (LiteralCheckerAcceptance.coreCall tag index fuel .zero (.add a a) code) (.succ .zero))) :
 Nonempty (Hilbert.Local T ctx G
  (.equal (LiteralCheckerAcceptance.coreCall tag index fuel .zero (.add b b) code) (.succ .zero))) := by
 have hd := localUnary (.add (.var 0) (.var 0)) a b hab
 have hd' : Hilbert.Local T ctx G (.equal (.add a a) (.add b b)) := by
  simpa only [GorbowStandardInstances.instantiate,GorbowSubstitution.substitute,Fin.cases_zero] using hd
 have he : Hilbert.Local T ctx G
  (.equal (LiteralCheckerAcceptance.coreCall tag index fuel .zero (.add a a) code)
   (LiteralCheckerAcceptance.coreCall tag index fuel .zero (.add b b) code)) := by
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
 exact ⟨localTrans _ _ _ (Hilbert.Local.mp (.base (Logic.symmetryRule T _ _)) he) ha⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.BaseProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.BaseProof
