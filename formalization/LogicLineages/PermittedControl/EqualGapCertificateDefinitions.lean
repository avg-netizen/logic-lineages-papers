module
public import LogicLineages.PermittedControl.InitialCodeDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

/-- Full literal finite certificate, less=0/equal=1/greater=2. -/
def equalGapCertificateCode (mu nu delta : Nat) : Nat :=
  if initialPassCode mu nu delta then pureCertificateCode mu nu (originalLeadingCode delta)
  else numericalComparison (rawProfileCode nu (originalLeadingCode delta))
    (rawProfileCode mu (originalLeadingCode delta))

/-- Both independently proved radii are paid directly, without a presumed
monotonicity theorem for the lcm-containing tail function. -/
def equalGapCertificateTailCode (mu nu delta B : Nat) : Nat :=
  max (thickBlockTail (20+rawNormCode delta+rawNormCode mu+rawNormCode nu) B)
    (pureCertificateTailCode mu nu (originalLeadingCode delta) B)

end LogicLineages.PermittedControl
