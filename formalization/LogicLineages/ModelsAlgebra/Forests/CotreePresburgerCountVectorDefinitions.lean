module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerPullbackStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCountVector
open CotreePresburger

/-- Choice-free, executable realization of a finite multiplicity vector.
Sorted finite enumeration is kept symbolic; no large vector is evaluated. -/
def realizeCounts {Q : Type} [Fintype Q] [LinearOrder Q] (v : Q → Nat) : List Q :=
  (elements Q).flatMap (fun q => List.replicate (v q) q)

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCountVector
