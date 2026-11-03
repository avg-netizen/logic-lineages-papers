module
public import LogicLineages.OrdinalComparison.ScalarCarrierAccountingDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AccountSemanticDeterminacy
open ScalarCarrierAccounting

/-- Ordered head-value trace of actual occurrence labels. This preserves
length/order/duplicates and intentionally does not identify actual sources. -/
noncomputable def headValues (xs : List Carrier) : List Ordinal := xs.map Carrier.head
end LogicLineages.OrdinalComparison.Source.AccountSemanticDeterminacy
