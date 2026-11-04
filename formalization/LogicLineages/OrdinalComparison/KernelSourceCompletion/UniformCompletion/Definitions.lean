module
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion

/-- Literal paper08 C_d. -/
def degreeConstant (d : Nat) : Nat := 1000*d*d

/-- Literal paper08 T_d for d>=3; values below degree three are unused. -/
def degreeThreshold : Nat → Nat
  | 0 => 16
  | d+1 => if d+1 ≤ 3 then 16 else
      max (degreeThreshold d) (100*degreeConstant d+100*(d+1))

def region (d c e : Nat) (j k : Int) (R t : Nat) : Prop :=
  degreeThreshold d ≤ t ∧
    degreeConstant d * (c+e+j.natAbs+k.natAbs+R+1) ≤ Phi t

/-- This degree/mass/input comes from the independent ORIGINAL schedule,
not the compensated companion's possibly different initial norm. -/
noncomputable def firstSuffix (d c t : Nat) : Ordinal :=
  actualMaximumPredecessor (Ordinal.omega0 ^ (d : Ordinal)) (Phi t-c)

noncomputable def sourceSignedDepth (d c : Nat) (j : Int) (t : Nat) : Int :=
  (sourceCount d c t : Int)+j

/-- Raw notation only; positive depth is required in every source conclusion. -/
noncomputable def sourceSignedValue (d c : Nat) (j : Int) (t : Nat) : Nat :=
  (Phi^[(sourceSignedDepth d c j t).toNat]) t

/-- One explicit tail paying the cross pair and both self pairs. -/
def equalityTail (d c e : Nat) (j k : Int) : Nat :=
  max (degreeThreshold d)
    (max (degreeConstant d * (c+e+j.natAbs+k.natAbs+1))
      (max (degreeConstant d * (2*c+2*j.natAbs+1))
        (degreeConstant d * (2*e+2*k.natAbs+1))))

end LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion
