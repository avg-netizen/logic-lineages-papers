module
public import LogicLineages.OrdinalComparison.CommonHeadLargeRowDefinitions
public import LogicLineages.OrdinalComparison.RawNormCodeDefinitions
public import LogicLineages.OrdinalComparison.EncodedFiniteTailDefinitions
public import LogicLineages.OrdinalComparison.EncodedCollapseDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.CommonHeadSmallFold
open CommonHeadLargeRow

noncomputable def closedValueCode (h c : Nat) : Nat :=
  encodedCollapseValue (encodedFiniteTail h (c-rawNormCode h))

noncomputable def foldedConstant (lam : Ordinal) (K : Int) (row : Row)
    (i : Fin row.length) (c : Nat) : Int :=
  K+(row[i].1)*(actualHeadValue lam c : Int)

def remaining (row : Row) (i : Fin row.length) : Row := row.eraseIdx i.val

noncomputable def smallValues (lam : Ordinal) (K : Int) (row : Row) : List Nat :=
  (List.range (threshold K row)).filter (fun c => actualOrdinalNorm lam ≤ c)

def smallValuesCode (h : Nat) (K : Int) (row : Row) : List Nat :=
  (List.range (threshold K row)).filter (fun c => rawNormCode h ≤ c)
end LogicLineages.OrdinalComparison.CommonHeadSmallFold
