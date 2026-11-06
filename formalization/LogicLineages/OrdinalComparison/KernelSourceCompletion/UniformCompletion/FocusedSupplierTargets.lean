module
public import LogicLineages.OrdinalComparison.KernelCounterCalibrationTargets
public import LogicLineages.OrdinalComparison.CounterSourceTheoremTargets
public import LogicLineages.OrdinalComparison.SmallKernelsTargets
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.Targets
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Targets
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.BroadBlockTargets
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.ScheduledWordTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.FocusedSupplierTargets

/-! Frozen supplier specifications for the focused uniform-separation closure.
The aliases retain the complete previously accepted source statements. They do
not replace the numerical source process or add any new premise to it. -/

def FiniteKernelInput : Prop :=
  LogicLineages.OrdinalComparison.Targets.ActualFiniteKernelInput

def KernelStartup : Prop :=
  LogicLineages.OrdinalComparison.CounterSourceTheorem.Targets.ActualKernelStartup

def SourceProcessBridge : Prop :=
  LogicLineages.OrdinalComparison.KernelSourceCompletion.Targets.SourceProcessBridge

def FirstBudgetCalibration : Prop := Targets.FirstBudgetCalibration

def SignedAgreementOnGenuineDomain : Prop := Targets.SignedAgreementOnGenuineDomain

def BroadUnsignedBlockCut : Prop := Targets.BroadUnsignedBlockCut

def ScheduledJointOrder : Prop := Targets.ScheduledJointOrder

def SourceInputMassOrder : Prop := Targets.SourceInputMassOrder

def UniformDepthAndOutputBounds : Prop := Targets.UniformDepthAndOutputBounds

def FourMulControl : Prop := ∀ u : Nat, 4*u < Phi u

def PhiEven : Prop := LogicLineages.OrdinalComparison.Targets.ActualPhiEven

def OmegaSuffixKernel : Prop :=
  LogicLineages.OrdinalComparison.Targets.ActualOmegaSuffixKernel

def OmegaSquaredSuffixCount : Prop :=
  LogicLineages.OrdinalComparison.Targets.ActualOmegaSquaredSuffixCount

def OmegaSquaredMassClasses : Prop :=
  LogicLineages.OrdinalComparison.Targets.ActualOmegaSquaredMassClasses

end LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.FocusedSupplierTargets
