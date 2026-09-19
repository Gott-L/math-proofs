import Std

namespace LiteralReview

theorem actual_literal_0 : "PANIC at " = String.mk [Char.ofNat 80, Char.ofNat 65, Char.ofNat 78, Char.ofNat 73, Char.ofNat 67, Char.ofNat 32, Char.ofNat 97, Char.ofNat 116, Char.ofNat 32] := by rfl
#print axioms actual_literal_0

theorem actual_literal_1 : " " = String.mk [Char.ofNat 32] := by rfl
#print axioms actual_literal_1

theorem actual_literal_2 : ":" = String.mk [Char.ofNat 58] := by rfl
#print axioms actual_literal_2

theorem actual_literal_3 : ": " = String.mk [Char.ofNat 58, Char.ofNat 32] := by rfl
#print axioms actual_literal_3

theorem actual_literal_4 : "Init.GetElem" = String.mk [Char.ofNat 73, Char.ofNat 110, Char.ofNat 105, Char.ofNat 116, Char.ofNat 46, Char.ofNat 71, Char.ofNat 101, Char.ofNat 116, Char.ofNat 69, Char.ofNat 108, Char.ofNat 101, Char.ofNat 109] := by rfl
#print axioms actual_literal_4

theorem actual_literal_5 : "_private.Init.GetElem.0.List.get!Internal" = String.mk [Char.ofNat 95, Char.ofNat 112, Char.ofNat 114, Char.ofNat 105, Char.ofNat 118, Char.ofNat 97, Char.ofNat 116, Char.ofNat 101, Char.ofNat 46, Char.ofNat 73, Char.ofNat 110, Char.ofNat 105, Char.ofNat 116, Char.ofNat 46, Char.ofNat 71, Char.ofNat 101, Char.ofNat 116, Char.ofNat 69, Char.ofNat 108, Char.ofNat 101, Char.ofNat 109, Char.ofNat 46, Char.ofNat 48, Char.ofNat 46, Char.ofNat 76, Char.ofNat 105, Char.ofNat 115, Char.ofNat 116, Char.ofNat 46, Char.ofNat 103, Char.ofNat 101, Char.ofNat 116, Char.ofNat 33, Char.ofNat 73, Char.ofNat 110, Char.ofNat 116, Char.ofNat 101, Char.ofNat 114, Char.ofNat 110, Char.ofNat 97, Char.ofNat 108] := by rfl
#print axioms actual_literal_5

theorem actual_literal_6 : "invalid index" = String.mk [Char.ofNat 105, Char.ofNat 110, Char.ofNat 118, Char.ofNat 97, Char.ofNat 108, Char.ofNat 105, Char.ofNat 100, Char.ofNat 32, Char.ofNat 105, Char.ofNat 110, Char.ofNat 100, Char.ofNat 101, Char.ofNat 120] := by rfl
#print axioms actual_literal_6

end LiteralReview
