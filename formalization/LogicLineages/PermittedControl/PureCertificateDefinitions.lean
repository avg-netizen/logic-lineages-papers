module
public import LogicLineages.PermittedControl.HighestPieceDefinitions
public import LogicLineages.PermittedControl.ThickBlockDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

/-- Literal three-way numerical sign: less=0, equal=1, greater=2. -/
def numericalComparison (a b : Nat) : Nat := if a < b then 0 else if a=b then 1 else 2

/-- Total raw-code pure-phase certificate. No semantic profile or phase
oracle is hidden in the computation. -/
def pureCertificateCode (mu nu E : Nat) : Nat :=
  if rawComparisonCode E (rawNoteEncode (ONote.ofNat 1))=1 then 1
  else match highestPieceCode mu nu E with
  | some n => numericalComparison (rawProfileCode nu n) (rawProfileCode mu n)
  | none => numericalComparison ((rawProfileCode nu (rawNoteEncode (ONote.ofNat 1))+1)/2)
      ((rawProfileCode mu (rawNoteEncode (ONote.ofNat 1))+1)/2)

def pureCertificateRadiusCode (mu nu E : Nat) : Nat :=
  100+4*(rawNormCode mu+rawNormCode nu+rawNormCode E)

def pureCertificateTailCode (mu nu E B : Nat) : Nat :=
  thickBlockTail (pureCertificateRadiusCode mu nu E) B

end LogicLineages.PermittedControl
