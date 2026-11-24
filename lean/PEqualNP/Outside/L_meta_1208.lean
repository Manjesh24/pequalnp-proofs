import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1208

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The circuit of the sketch for the graph n8-059 (edges 01 02 13 24 35 46 57): wire `8` is
`x1 OR x2`, wire `9` is `x0 AND wire 8`, wire `10` is `x1 AND x3`, wire `11` is `x2 OR x6`,
wire `12` is `x4 AND wire 11`, wire `13` is `x3 OR x7`, wire `14` is `x5 AND wire 13`,
wire `15` is `wire 9 OR wire 10`, wire `16` is `wire 15 OR wire 12` and wire `17` is
`wire 16 OR wire 14`, which is the output. -/
def C0 : Circuit :=
  ⟨[ ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 3]⟩,
      ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [4, 11]⟩, ⟨GateOp.or, [3, 7]⟩,
      ⟨GateOp.and, [5, 13]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [15, 12]⟩,
      ⟨GateOp.or, [16, 14]⟩ ], 17⟩

theorem ok0 : Monotone2 C0 := by
  intro g hg
  simp only [C0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ofFn8 (x : Fin 8 → Bool) :
    List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
  simp [List.ofFn_succ]

theorem ev0 : ∀ (b0 b1 b2 b3 b4 b5 b6 b7 : Bool),
    C0.eval [b0, b1, b2, b3, b4, b5, b6, b7] =
      ((b0 && b1) || (b0 && b2) || (b1 && b3) || (b2 && b4) || (b3 && b5) || (b4 && b6) ||
        (b5 && b7)) := by
  decide +kernel

end PEqualNP.Outside.L_meta_1208

theorem PEqualNP.Outside.L_meta_1208 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 7)) x :=
  ⟨PEqualNP.Outside.L_meta_1208.C0, PEqualNP.Outside.L_meta_1208.ok0, by decide,
    fun x => by
      rw [PEqualNP.Outside.L_meta_1208.ofFn8]
      exact PEqualNP.Outside.L_meta_1208.ev0 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)⟩
