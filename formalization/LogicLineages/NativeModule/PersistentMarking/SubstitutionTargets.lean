module

public import LogicLineages.NativeModule.PersistentMarking.SpineSyntax

@[expose] public section

namespace LogicLineages.PersistentMarking.SubstitutionTargets
open Spine

def ShiftZero : Prop := ∀ t cutoff, shift 0 cutoff t = t
def ShiftArgsZero : Prop := ∀ ts cutoff, shiftArgs 0 cutoff ts = ts
def ShiftAdd : Prop := ∀ t a b cutoff,
  shift a cutoff (shift b cutoff t) = shift (b+a) cutoff t
def ShiftArgsAdd : Prop := ∀ ts a b cutoff,
  shiftArgs a cutoff (shiftArgs b cutoff ts) = shiftArgs (b+a) cutoff ts
def EmptySubstitution : Prop := ∀ t depth, substitute .nil depth t = t
def EmptyArgsSubstitution : Prop := ∀ ts depth, substituteArgs .nil depth ts = ts
def ShiftType : Prop := ∀ t amount cutoff, (shift amount cutoff t).type = t.type
end LogicLineages.PersistentMarking.SubstitutionTargets
