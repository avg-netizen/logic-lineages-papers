module

public import LogicLineages.PersistentMarking.NumberedWindowAddressApplication
public import LogicLineages.PersistentMarking.NumberedWindowClassApplicationPath

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowApplicationMatch
open NumberedWindowAddressAlgorithm (addressView)
open NumberedWindowAddressApplication (application arrowView)
open NumberedWindowScalarAlgorithm (Settings least)
open NumberedWindowClassApplicationPath (liftPath)

/-- Compute the earlier application's original canonical address and
lift the supplied positive certificate. The transformed path keeps the
original full context and changes only the result fiber to the codomain. -/
def matchingCertificate (s : Settings) (source argument certificate : Nat) : Option (Nat × Nat) := do
  let (context,functionType,_) ← addressView source
  let (domain,result) ← arrowView functionType
  let (_,_,input) ← addressView argument
  let before ← application s source argument
  let (_,_,start) ← addressView before
  let (_,output) ← liftPath (least s context result) domain result input start certificate
  pure (before,output)

end LogicLineages.PersistentMarking.NumberedWindowApplicationMatch
