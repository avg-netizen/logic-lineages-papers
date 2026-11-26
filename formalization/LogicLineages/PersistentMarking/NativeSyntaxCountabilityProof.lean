import LogicLineages.PersistentMarking.NativeSyntaxCountabilityTargets
import LogicLineages.PersistentMarking.NumberedWindowOrdinaryDomainProof
import LogicLineages.PersistentMarking.NumberedWindowArithmeticTermCodeChecks

namespace LogicLineages.PersistentMarking.NativeSyntaxCountabilityProof
open NumberedWindowSyntax NumberedWindowOrdinaryTranslation
open NumberedWindowArithmeticTermCode NativeSyntaxCountabilityTargets

mutual
private theorem termRoundtrip (q : Spine.Expr) (Q : NTerm) (h : tr q = some Q) :
    readOrdinary Q = some q := by
  cases q with
  | free σ x =>
    have e : NTerm.free σ x = Q := Option.some.inj h
    subst Q
    rfl
  | bound σ i =>
    have e : NTerm.bound σ i = Q := Option.some.inj h
    subst Q
    rfl
  | lam σ body =>
    cases translated : tr body with
    | none => simp [tr, translated] at h
    | some out =>
      have e : NTerm.lam σ out = Q := by
        simpa only [tr, translated, Option.map_some, Option.some.injEq] using h
      subst Q
      simp [readOrdinary, termRoundtrip body out translated]
  | head f base =>
    cases translated : trArgs base with
    | none => simp [tr, translated] at h
    | some out =>
      have e : NTerm.ordinary f out = Q := by
        simpa only [tr, translated, Option.map_some, Option.some.injEq] using h
      subst Q
      simp [readOrdinary, argsRoundtrip base out translated]
  | marked f τ base extras => simp [tr] at h
termination_by sizeOf q

private theorem argsRoundtrip (bs : Spine.Args) (As : NArgs) (h : trArgs bs = some As) :
    readOrdinaryArgs As = some bs := by
  cases bs with
  | nil =>
    have e : NArgs.nil = As := Option.some.inj h
    subst As
    rfl
  | cons q qs =>
    cases first : tr q with
    | none => simp [trArgs, first] at h
    | some out =>
      cases rest : trArgs qs with
      | none => simp [trArgs, first, rest] at h
      | some outs =>
        have e : NArgs.cons out outs = As := by
          simpa [trArgs, first, rest] using h
        subst As
        simp [readOrdinaryArgs, termRoundtrip q out first, argsRoundtrip qs outs rest]
termination_by sizeOf bs
end

theorem roundtrip : OrdinaryLiteralRoundtrip := ⟨termRoundtrip, argsRoundtrip⟩

theorem countableSyntax : ClosedNativeCountability := by
  intro S τ q r hcode
  obtain ⟨Q, hQ⟩ :=
    (NumberedWindowOrdinaryDomainProof.termDomain q.val).mpr q.property.1.2.1
  obtain ⟨R, hR⟩ :=
    (NumberedWindowOrdinaryDomainProof.termDomain r.val).mpr r.property.1.2.1
  have encoded : encodeTerm Q = encodeTerm R := by
    simpa [nativeCode, hQ, hR] using hcode
  have decoded := congrArg decodeTerm encoded
  have codec := NumberedWindowArithmeticTermCodeChecks.exact_TermCodec.2.1
  rw [codec Q, codec R] at decoded
  have same := Option.some.inj decoded
  apply Subtype.ext
  have qr := termRoundtrip q.val Q hQ
  rw [same, termRoundtrip r.val R hR] at qr
  exact (Option.some.inj qr).symm

end LogicLineages.PersistentMarking.NativeSyntaxCountabilityProof
