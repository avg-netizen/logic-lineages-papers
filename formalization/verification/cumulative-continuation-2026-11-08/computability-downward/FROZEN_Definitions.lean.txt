module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownward
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open SourceComputabilityFormulaSupportProof InternalComputabilityApplication InternalAccessibilityRules
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The original typed, same-Gamma application domain. No computability or
accessibility assumption occurs in this arithmetic formula. -/
def domain {α : Type} (comp : JointGammaComputability.Data) (context : Nat)
    (sigma tau : Ty) (f a : OTerm α) : Formula α :=
  (typed comp (.arrow sigma tau) (numeral context) f ⊓
    typed comp sigma (numeral context) a) ⊓ guarded comp f a

def applicationExists {α : Type} (comp : JointGammaComputability.Data) (context : Nat)
    (sigma tau : Ty) (f a : OTerm α) : Formula α :=
  existsOne (accepted comp sigma tau (numeral context)
    (f.relabel Sum.inl) (a.relabel Sum.inl) (.var (.inr 0)))

/-- Three local arithmetic derivations. These are explicit hypotheses of the
relative theorem, not fields added to the original source presentation. -/
structure ArithmeticRules (src : SourcePresentation.Data) (comp : JointGammaComputability.Data)
    (context : Nat) : Prop where
  typedDown : ∀ (α : Type) (tau : Ty) (f g : OTerm α),
    Nonempty (Derivation (SourcePresentation.sourceBody src context) []
      ((typed comp tau (numeral context) f ⊓ edge src false context f g).imp
        (typed comp tau (numeral context) g)))
  guardBack : ∀ (α : Type) (tau : Ty) (f g a : OTerm α),
    Nonempty (Derivation (SourcePresentation.sourceBody src context) []
      (((typed comp tau (numeral context) f ⊓ edge src false context f g) ⊓
        guarded comp g a).imp (guarded comp f a)))
  applicationTotal : ∀ (α : Type) (sigma tau : Ty) (f a : OTerm α),
    Nonempty (Derivation (SourcePresentation.sourceBody src context) []
      ((domain comp context sigma tau f a).imp
        (applicationExists comp context sigma tau f a)))

/-- Local compatibility of the original positive relation with application.
Every premise is arithmetic; the original existential certificate is retained. -/
def ApplicationCompatibility (src : SourcePresentation.Data)
    (comp : JointGammaComputability.Data) (context : Nat) : Prop :=
  ∀ (α : Type) (sigma tau : Ty) (f g a out other : OTerm α),
  Nonempty (Derivation (SourcePresentation.sourceBody src context) []
    (((domain comp context sigma tau f a ⊓ edge src false context f g) ⊓
      (accepted comp sigma tau (numeral context) f a out ⊓
        accepted comp sigma tau (numeral context) g a other)).imp
      (edge src false context out other)))

/-- The exact five inputs of the original application-path transformer. -/
def liftArguments {α : Type} (context : Nat) (sigma tau : Ty)
    (a witness : OTerm α) : Fin 5 → OTerm α :=
  ![numeral context,numeral (NumberedLeastCodeRepresentative.typeNumber sigma),
    numeral (NumberedLeastCodeRepresentative.typeNumber tau),a,witness]

/-- The missing source-specific graph theorem, stated without reflection.
The supplied original certificate is transformed by a concrete Program, and
its literal graph output must be an accepted original output certificate. -/
def CertifiedApplicationLift (src : SourcePresentation.Data)
    (comp : JointGammaComputability.Data) (lift : Program 5) (context : Nat) : Prop :=
  ∀ (α : Type) (sigma tau : Ty) (f g a out other witness lifted : OTerm α),
  Nonempty (Derivation (SourcePresentation.sourceBody src context) []
    (((domain comp context sigma tau f a ⊓ certificate src false context f g witness) ⊓
      ((accepted comp sigma tau (numeral context) f a out ⊓
        accepted comp sigma tau (numeral context) g a other) ⊓
        programGraph lift lifted (liftArguments context sigma tau a witness))).imp
      (certificate src false context out other lifted)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownward
