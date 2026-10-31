module
public import LogicLineages.OrdinalComparison.WWSourceSyntaxQueryTargets
public import LogicLineages.OrdinalComparison.WWQuerySyntaxCodeProof
public import LogicLineages.OrdinalComparison.WWEncodedCounterBoundProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ForwardTranslation

theorem sourceSyntaxQueryNormalization : Targets.SourceSyntaxQueryNormalization := by
  intro Γ τ υ p strict a b
  unfold compileSourceSyntaxQuery compileSourceQuery
  cases ha : AdmissibleAssignment.assignment p a with
  | none => simp
  | some av =>
    cases hb : AdmissibleAssignment.assignment p b with
    | none => simp
    | some bv =>
      cases hac : compileVector av with
      | none => simp [hac]
      | some ac =>
        cases hbc : compileVector bv with
        | none => simp [hac, hbc]
        | some bc =>
          simpa [hac, hbc] using congrArg some (querySyntaxNormalizationCorrect _ _ _ (fun c => SourceTypedPorts.variableIndex c.2.1) strict ac bc)

theorem sourceSyntaxCodeNormalization : Targets.SourceSyntaxCodeNormalization := by
  intro Γ τ υ p strict a b
  have h := sourceSyntaxQueryNormalization Γ τ υ p strict a b
  unfold compileSourceSyntaxCode compileSourceCode
  rw [← h]
  cases hq : compileSourceSyntaxQuery p strict a b with
  | none => rfl
  | some q => simp [normalizeAritySyntaxCode, decodeArityQuery]

theorem aritySyntaxNormalizationPrimitiveRecursive : Targets.AritySyntaxNormalizationPrimitiveRecursive := by
  have hd : Primrec decodeArityQuery :=
    Primrec.option_getD.comp Primrec.decode (Primrec.const (0, false, (0, []), (0, [])))
  exact Primrec.encode.comp ((Primrec.fst.comp hd).pair
    (querySyntaxNormalizationPrimitiveRecursive.comp (Primrec.snd.comp hd)))
end LogicLineages.OrdinalComparison.Source.ForwardTranslation
