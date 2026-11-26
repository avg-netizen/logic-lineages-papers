module

public import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowAuxExchangeLiftTargets
open NumberedWindowAddressAlgorithm (typeBit)
open NumberedWindowAnnotationAlgorithm (arrow)
open NumberedWindowAtomicApplicationTargets (auxRaw)
open NumberedWindowExchangeAlgorithm (bits)
open NumberedWindowExchangeAtoms (HeadPairs)
open NumberedWindowLexicalAlgorithm (typed)
open NumberedWindowScalarAlgorithm (Settings admitted edge)
open NumberedWindowSyntaxAlgorithm (syntaxBits)

/-- The original type decoder must accept both explicit tag-six type fields. -/
def ExactAuxTermSyntax : Prop :=
  ∀ dom cod fn arg, (syntaxBits (auxRaw dom cod fn arg)).1 =
    (typeBit dom && typeBit cod && (syntaxBits fn).1 && (syntaxBits arg).1)

/-- Both application children are typed in exactly the same context. -/
def ExactAuxTermTyping : Prop :=
  ∀ ctx dom cod fn arg, typed ctx cod (auxRaw dom cod fn arg) =
    (typeBit dom && typeBit cod && typed ctx (arrow dom cod) fn && typed ctx dom arg)

/-- All type, head, and lexical conditions from the original window checker. -/
def ExactAuxWindowAdmission : Prop :=
  ∀ (s : Settings) ctx dom cod fn arg, admitted s ctx cod (auxRaw dom cod fn arg) =
    (typeBit dom && typeBit cod && s.window.1.contains dom && s.window.1.contains cod &&
      admitted s ctx (arrow dom cod) fn && admitted s ctx dom arg)

/-- A function-side exchange preserves the literal argument and both type fields. -/
def ExactAuxExchangeLift : Prop :=
  ∀ (hp : HeadPairs) dom cod fn fn' arg, typeBit dom = true → typeBit cod = true →
    (syntaxBits arg).1 = true → (bits hp fn fn').1 = true →
    (bits hp (auxRaw dom cod fn arg) (auxRaw dom cod fn' arg)).1 = true

/-- The same lift with both original endpoint window checks paid. -/
def ExactAuxWindowEdgeLift : Prop :=
  ∀ (s : Settings) ctx dom cod fn fn' arg,
    typeBit dom = true → typeBit cod = true →
    s.window.1.contains dom = true → s.window.1.contains cod = true →
    admitted s ctx dom arg = true → edge s ctx (arrow dom cod) fn fn' = true →
    edge s ctx cod (auxRaw dom cod fn arg) (auxRaw dom cod fn' arg) = true

end LogicLineages.PersistentMarking.NumberedWindowAuxExchangeLiftTargets
