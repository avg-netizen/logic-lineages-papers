module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TermCodecDefinitions
public import Mathlib.Computability.Primrec.Basic
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TermCodecTargets

def LiteralTermRoundTrip : Prop := ∀ t : Term, TermCodec.decode t.encode = t
def EveryOriginalCodeRoundTrip : Prop := ∀ code : Nat, (TermCodec.decode code).encode = code
def OriginalEncodeInjectivity : Prop := Function.Injective Term.encode
/-- A standard primitive coding whose encoder is exactly the original encoder.
This does not assume computability of any syntax operation or BASE solver. -/
def LiteralPrimitiveCoding : Prop := ∃ coding : Primcodable Term,
  ∀ t : Term, coding.toEncodable.encode t = t.encode

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TermCodecTargets
