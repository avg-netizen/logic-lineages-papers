module
public import LogicLineages.OrdinalComparison.ComparisonExpansionTargets
public import LogicLineages.OrdinalComparison.PositiveExprCodeProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonExpansion

private theorem positive_injective : Function.Injective positiveExprEncode := by
  intro E F h
  have hd := congrArg positiveExprDecode h
  rw [positiveExprCodeRoundTrip E,positiveExprCodeRoundTrip F] at hd
  exact Option.some.inj hd

private theorem word_injective : Function.Injective (fun w : List (NONote × Nat) =>
    encodePrincipalKernelWord (comparisonRawWord w)) := by
  have hp : Function.Injective (fun p : NONote × Nat => (rawNoteEncode p.1.1,p.2)) := by
    intro p q h
    have hN : p.1=q.1 := by
      apply Subtype.ext
      have he := congrArg (fun z : Nat × Nat => rawNoteDecode z.1) h
      simpa only [rawNoteDecodeEncode p.1.1,rawNoteDecodeEncode q.1.1] using he
    have hc := congrArg (fun z : Nat × Nat => z.2) h
    exact Prod.ext hN hc
  intro w v h
  apply (List.map_injective_iff.mpr hp)
  simpa only [encodePrincipalKernelWord,comparisonRawWord,List.map_map,Function.comp_def] using h

theorem source_injective : Targets.LiteralSourceEncodingInjective := by
  intro E F h
  cases E with
  | positive E =>
    cases F with
    | positive F =>
      have he : positiveExprEncode E=positiveExprEncode F := by
        change 2*positiveExprEncode E=2*positiveExprEncode F at h
        omega
      exact congrArg OneVariableComparisonExpr.positive (positive_injective he)
    | range w F =>
      change 2*positiveExprEncode E=2*Nat.pair _ _+1 at h
      omega
  | range w E =>
    cases F with
    | positive F =>
      change 2*Nat.pair _ _+1=2*positiveExprEncode F at h
      omega
    | range v F =>
      have he : Nat.pair (Encodable.encode (encodePrincipalKernelWord (comparisonRawWord w))) (positiveExprEncode E)=
          Nat.pair (Encodable.encode (encodePrincipalKernelWord (comparisonRawWord v))) (positiveExprEncode F) := by
        change 2*Nat.pair _ _+1=2*Nat.pair _ _+1 at h
        omega
      have hW := congrArg (fun n : Nat => n.unpair.1) he
      have hE := congrArg (fun n : Nat => n.unpair.2) he
      simp only [Nat.unpair_pair] at hW hE
      have hw : w=v := word_injective (Encodable.encode_injective hW)
      have hEF : E=F := positive_injective hE
      subst v F
      rfl

end LogicLineages.OrdinalComparison.ComparisonExpansion
