module
public import LogicLineages.OrdinalComparison.SourceLiteralWeakWrapperCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceLiteralWeakWrapperCode.Targets
open ParametricLiteralWeakWrapper

def ExactEncoding : Prop := ∀ (Γ : List Ty) (t : OriginalTerm Γ .ground),
  identityCode (SyntaxCode.encodeTerm t)=SyntaxCode.encodeTerm (identityApply t) ∧
  constantCode (SyntaxCode.encodeTerm t)=SyntaxCode.encodeTerm (constantApply t)

def UniformPrimitiveRecursive : Prop := Primrec identityCode ∧ Primrec constantCode

def FragmentPreservation : Prop := ∀ (Γ : List Ty) (t : OriginalTerm Γ .ground),
  SourceGroundBinderFragment.Fragment t →
  SourceGroundBinderFragment.Fragment (identityApply t) ∧
  SourceGroundBinderFragment.Fragment (constantApply t)

def InternalLevelPreservation : Prop := ∀ (Γ : List Ty) (t : OriginalTerm Γ .ground),
  SourceMachineRawValuations.AllGround Γ → SourceGroundBinderFragment.Fragment t →
  SourceClasses.InternalLevelBound 1 (identityApply t) ∧
  SourceClasses.InternalLevelBound 1 (constantApply t)
end LogicLineages.OrdinalComparison.Source.SourceLiteralWeakWrapperCode.Targets
