module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.RowProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation.StepSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.EmitterProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open RelationalSyntaxDepthTransport.ConstructorStepTargets
theorem oneNotTwo (T : Sentence → Prop) (ctx : Nat) :
 Nonempty (Derivation T (.neg (.equal (Term.numeral (n := ctx) 1) (Term.numeral 2)))) := by
 let H : Formula ctx := .equal (Term.numeral 1) (Term.numeral 2)
 let F : Formula ctx := .equal (.succ .zero) .zero
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 have hi : Hilbert.Local T ctx [H] (.equal .zero (.succ .zero)) :=
  .mp (.base (.arithmetic (.succInjective .zero (.succ .zero)))) hh
 have hm : Derivation T (.imp H F) := (HistoryOrder.StepProof.localSym _ _ hi).discharge.finish
 exact ⟨.mp (.mp (HistoryLengthConservation.StepSupportProof.contraposition H F) hm) (.arithmetic (.succNotZero .zero))⟩
theorem formula {n ctx : Nat} (p : Program n) (etag ptag ctag : Nat)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (bound rest token raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (UniformClosedSubstitutionEmit.emitCall etag
   (UniformClosedSubstitutionEmit.stateValue ptag ctag (Term.numeral 1) bound rest) token raw)
   (UniformClosedSubstitutionEmit.singletonValue ctag token))) := by
 obtain ⟨h⟩ := UniformClosedSubstitutionEmit.NonIndexProof.otherKind p etag ptag ctag he hp hc (Term.numeral 1) bound rest token raw
 obtain ⟨hn⟩ := oneNotTwo (GorbowPRNumeralCalculation.Theory p) ctx
 exact ⟨.mp (.mp h (.arithmetic (.succNotZero .zero))) hn⟩
/-- All non-marker original constructor tokens are copied literally. The single
excluded finite marker case is paid by MarkerProof, not dropped from final scope. -/
theorem constructor {n ctx : Nat} (p : Program n) (etag ptag ctag : Nat)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ctor : Constructor) (hmarker : ctor ≠ .term 0) (bound rest raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (UniformClosedSubstitutionEmit.emitCall etag
   (UniformClosedSubstitutionEmit.stateValue ptag ctag (Term.numeral (kind ctor)) bound rest)
   (Term.numeral (token ctor)) raw)
   (UniformClosedSubstitutionEmit.singletonValue ctag (Term.numeral (token ctor))))) := by
 cases ctor with
 | term i =>
  fin_cases i
  · exact False.elim (hmarker rfl)
  · exact UniformClosedSubstitutionEmit.NonIndexProof.termSuccessor p etag ptag ctag he hp hc bound rest (Term.numeral 0) raw
  · exact UniformClosedSubstitutionEmit.NonIndexProof.termSuccessor p etag ptag ctag he hp hc bound rest (Term.numeral 1) raw
  · exact UniformClosedSubstitutionEmit.NonIndexProof.termSuccessor p etag ptag ctag he hp hc bound rest (Term.numeral 2) raw
  · exact UniformClosedSubstitutionEmit.NonIndexProof.termSuccessor p etag ptag ctag he hp hc bound rest (Term.numeral 3) raw
  · exact UniformClosedSubstitutionEmit.NonIndexProof.termSuccessor p etag ptag ctag he hp hc bound rest (Term.numeral 4) raw
 | formula i => exact formula p etag ptag ctag he hp hc bound rest (Term.numeral i.val) raw
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.EmitterProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.EmitterProof
