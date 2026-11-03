module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeParserTableTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeParserTableSupportProof
open NumberedNumericDecoding NumberedCodeParserTable

@[simp] theorem anyConstant {A : Type} (o : Option A) (b : Bool) : o.any (fun _ => b)= (o.isSome && b) := by
  cases o <;> rfl

theorem calibration (n bound fuel : Nat) : ∀ value, value≤bound →
    lookup (codeTable n bound fuel) value = (codeParse n fuel value).isSome := by
  induction fuel with
  | zero =>
    intro value hv
    simp [lookup,codeTable,codeParse,show value<bound+1 by omega]
  | succ fuel ih =>
    intro value hv
    have hl0 : (Nat.unpair value).1≤bound := (Nat.unpair_left_le value).trans hv
    have hr0 : (Nat.unpair value).2≤bound := (Nat.unpair_right_le value).trans hv
    have hl1 : (Nat.unpair (Nat.unpair value).2).1≤bound := (Nat.unpair_left_le (Nat.unpair value).2).trans hr0
    have hr1 : (Nat.unpair (Nat.unpair value).2).2≤bound := (Nat.unpair_right_le (Nat.unpair value).2).trans hr0
    have hl2 : (Nat.unpair (Nat.unpair (Nat.unpair value).2).2).1≤bound := (Nat.unpair_left_le (Nat.unpair (Nat.unpair value).2).2).trans hr1
    have hr2 : (Nat.unpair (Nat.unpair (Nat.unpair value).2).2).2≤bound := (Nat.unpair_right_le (Nat.unpair (Nat.unpair value).2).2).trans hr1
    have hl3 : (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair value).2).2).2).1≤bound := (Nat.unpair_left_le (Nat.unpair (Nat.unpair (Nat.unpair value).2).2).2).trans hr2
    have hr3 : (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair value).2).2).2).2≤bound := (Nat.unpair_right_le (Nat.unpair (Nat.unpair (Nat.unpair value).2).2).2).trans hr2
    have hl4 : (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair value).2).2).2).2).1≤bound := (Nat.unpair_left_le (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair value).2).2).2).2).trans hr3
    have hr4 : (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair value).2).2).2).2).2≤bound := (Nat.unpair_right_le (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair value).2).2).2).2).trans hr3
    have hl5 : (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair value).2).2).2).2).2).1≤bound := (Nat.unpair_left_le (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair value).2).2).2).2).2).trans hr4
    have hr5 : (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair value).2).2).2).2).2).2≤bound := (Nat.unpair_right_le (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair value).2).2).2).2).2).trans hr4
    have hl6 : (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair value).2).2).2).2).2).2).1≤bound := (Nat.unpair_left_le (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair value).2).2).2).2).2).2).trans hr5
    have hr6 : (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair value).2).2).2).2).2).2).2≤bound := (Nat.unpair_right_le (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair value).2).2).2).2).2).2).trans hr5
    change (((List.range (bound+1)).map (codeNext n (codeTable n bound fuel)))[value]?).getD false = _
    simp only [List.getElem?_map,List.getElem?_range (show value<bound+1 by omega),Option.map_some,Option.getD_some]
    generalize ht : (Nat.unpair value).1=tag
    rcases tag with _ | _ | _ | _ | _ | _ | _ | _ | tag
    all_goals
      simp (disch := assumption)
        [codeNext,codeParse,ht,ih,bind,pure,Option.isSome_bind,Bool.and_assoc]
    all_goals first | rfl | (split <;> simp_all)

theorem validatedSuccess (n value : Nat) : (decodeCode n value).isSome = (codeParse n (value+1) value).isSome := by
  cases h : codeParse n (value+1) value with
  | none => simp [decodeCode,h]
  | some code =>
    have he := NumberedRawParserSoundnessProof.rawCodeSound n (value+1) value code h
    simp [decodeCode,h,he,Option.filter]

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeParserTableSupportProof
