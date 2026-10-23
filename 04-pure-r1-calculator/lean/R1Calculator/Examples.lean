import R1Calculator.Ordinal
import R1Calculator.Patterns

/- Generated from examples/endpoint-fixtures.json by scripts/generate_examples.py.
Expected endpoints are explicit fixtures, not outputs of Python endpoint. -/
namespace R1Calculator.Examples

theorem endpoint_fixture_0 :
    endpoint ONote.zero = ONote.zero := by decide

theorem endpoint_fixture_1 :
    endpoint (ONote.oadd ONote.zero 7 ONote.zero) = (ONote.oadd ONote.zero 7 ONote.zero) := by decide

theorem endpoint_fixture_2 :
    endpoint (ONote.oadd (ONote.oadd ONote.zero 1 ONote.zero) 1 ONote.zero) = (ONote.oadd (ONote.oadd ONote.zero 1 ONote.zero) 1 (ONote.oadd ONote.zero 1 ONote.zero)) := by decide

theorem endpoint_fixture_3 :
    endpoint (ONote.oadd (ONote.oadd ONote.zero 2 ONote.zero) 1 ONote.zero) = (ONote.oadd (ONote.oadd ONote.zero 2 ONote.zero) 1 (ONote.oadd ONote.zero 2 ONote.zero)) := by decide

theorem endpoint_fixture_4 :
    endpoint (ONote.oadd (ONote.oadd (ONote.oadd ONote.zero 1 ONote.zero) 1 ONote.zero) 1 ONote.zero) = (ONote.oadd (ONote.oadd (ONote.oadd ONote.zero 1 ONote.zero) 1 ONote.zero) 1 (ONote.oadd (ONote.oadd ONote.zero 1 ONote.zero) 1 (ONote.oadd ONote.zero 1 ONote.zero))) := by decide

theorem endpoint_fixture_5 :
    endpoint (ONote.oadd (ONote.oadd (ONote.oadd ONote.zero 1 ONote.zero) 1 (ONote.oadd ONote.zero 1 ONote.zero)) 1 ONote.zero) = (ONote.oadd (ONote.oadd (ONote.oadd ONote.zero 1 ONote.zero) 1 (ONote.oadd ONote.zero 1 ONote.zero)) 1 (ONote.oadd (ONote.oadd ONote.zero 1 ONote.zero) 1 (ONote.oadd ONote.zero 2 ONote.zero))) := by decide

theorem endpoint_fixture_6 :
    endpoint (ONote.oadd (ONote.oadd (ONote.oadd ONote.zero 1 ONote.zero) 2 ONote.zero) 1 ONote.zero) = (ONote.oadd (ONote.oadd (ONote.oadd ONote.zero 1 ONote.zero) 2 ONote.zero) 1 (ONote.oadd (ONote.oadd ONote.zero 1 ONote.zero) 2 (ONote.oadd ONote.zero 1 ONote.zero))) := by decide

theorem endpoint_fixture_7 :
    endpoint (ONote.oadd (ONote.oadd (ONote.oadd ONote.zero 1 ONote.zero) 1 ONote.zero) 2 ONote.zero) = (ONote.oadd (ONote.oadd (ONote.oadd ONote.zero 1 ONote.zero) 1 ONote.zero) 2 (ONote.oadd (ONote.oadd ONote.zero 1 ONote.zero) 1 (ONote.oadd ONote.zero 1 ONote.zero))) := by decide

theorem endpoint_fixture_8 :
    endpoint (ONote.oadd (ONote.oadd ONote.zero 3 ONote.zero) 1 (ONote.oadd (ONote.oadd ONote.zero 2 ONote.zero) 4 ONote.zero)) = (ONote.oadd (ONote.oadd ONote.zero 3 ONote.zero) 1 (ONote.oadd (ONote.oadd ONote.zero 2 ONote.zero) 4 (ONote.oadd ONote.zero 2 ONote.zero))) := by decide

theorem endpoint_fixture_9 :
    endpoint (ONote.oadd (ONote.oadd (ONote.oadd ONote.zero 2 ONote.zero) 1 ONote.zero) 1 ONote.zero) = (ONote.oadd (ONote.oadd (ONote.oadd ONote.zero 2 ONote.zero) 1 ONote.zero) 1 (ONote.oadd (ONote.oadd ONote.zero 2 ONote.zero) 1 (ONote.oadd ONote.zero 2 ONote.zero))) := by decide

example : coversCheck (discrete 2) (chain 2) = true := by decide
example : embedsCheck (discrete 2) (chain 2) = false := by decide
example : markedCoversCheck (discrete 2) (discrete 2) = false := by decide

end R1Calculator.Examples
